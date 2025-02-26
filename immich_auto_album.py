
"""Python script for creating albums in Immich from folder names in an external library."""

from typing import Tuple
import argparse
import logging
import sys
import fnmatch
import os
import datetime
from collections import defaultdict, OrderedDict
import json
import random
import sqlite3
from urllib.error import HTTPError

import regex
import yaml

import urllib3
import requests

# Script Constants

# Constants holding script run modes
# Create albums based on folder names and script arguments
SCRIPT_MODE_CREATE = "CREATE"
# Create album names based on folder names, but delete these albums
SCRIPT_MODE_CLEANUP = "CLEANUP"
# Delete ALL albums
SCRIPT_MODE_DELETE_ALL = "DELETE_ALL"

# Environment variable to check if the script is running inside Docker
ENV_IS_DOCKER = "IS_DOCKER"

# List of allowed share user roles
SHARE_ROLES = ["editor", "viewer"]

# Immich API request timeout
REQUEST_TIMEOUT_DEFAULT = 20

# Constants for album thumbnail setting
ALBUM_THUMBNAIL_RANDOM_ALL = "random-all"
ALBUM_THUMBNAIL_SETTINGS = ["first", "last", "random"]
ALBUM_THUMBNAIL_SETTINGS_GLOBAL = ALBUM_THUMBNAIL_SETTINGS + [ALBUM_THUMBNAIL_RANDOM_ALL]
ALBUM_THUMBNAIL_STATIC_INDICES = {
    "first": 0,
    "last": -1,
}

# File name to use for album properties files
ALBUMPROPS_FILE_NAME = '.albumprops'

class AlbumMergeException(Exception):
    """Error thrown when trying to override an existing property"""

# Disable pylint rule for too many instance attributes
# pylint: disable=R0902
class AlbumModel:
    """Model of an album with all properties necessary for handling albums in the scope of this script"""
    # Album Merge Mode indicating only properties should be merged that are
    # not already set in the merge target
    ALBUM_MERGE_MODE_EXCLUSIVE = 1
    # Same as ALBUM_MERGE_MODE_EXCLUSIVE, but also raises an error
    # if attempting to overwrite an existing property when merging
    ALBUM_MERGE_MODE_EXCLUSIVE_EX = 2
    # Override any property in the merge target if already exists
    ALBUM_MERGE_MODE_OVERRIDE = 3
    # List of class attribute names that are relevant for album properties handling
    # This list is used for album model merging and validation
    ALBUM_PROPERTIES_VARIABLES = ['override_name', 'description', 'share_with', 'thumbnail_setting', 'sort_order', 'archive', 'comments_and_likes_enabled']

    def __init__(self, name : str):
        # The album ID, set after it was created
        self.id = None
        # The album name
        self.name = name
        # The override album name, takes precedence over name for album creation
        self.override_name = None
        # The description to set for the album
        self.description = None
        # A list of dicts with Immich assets
        self.assets = []
        # a list of dicts with keys user and role, listing all users and their role to share the album with
        self.share_with = []
        # Either a fully qualified asset path or one of 'first', 'last', 'random'
        self.thumbnail_setting = None
        # Sorting order for this album, 'asc' or 'desc'
        self.sort_order = None
        # Boolean indicating whether assets in this album should be archived after adding
        self.archive = None
        # Boolean indicating whether assets in this albums can be commented on and liked
        self.comments_and_likes_enabled = None

    def get_album_properties_dict(self) -> dict:
        """
        Returns this class' attributes relevant for album properties handling
        as a dictionary

        Returns
        ---------
            A dictionary of all album properties
        """
        props = dict(vars(self))
        for prop in list(props.keys()):
            if prop not in AlbumModel.ALBUM_PROPERTIES_VARIABLES:
                del props[prop]
        return props

    def __str__(self) -> str:
        """
        Returns a string representation of this most important album properties

        Returns
        ---------
            A string for printing this album model's properties
        """
        return str(self.get_album_properties_dict())

    def get_asset_uuids(self) -> list:
        """ 
        Gathers UUIDs of all assets and returns them

        Returns
        ---------
            A list of asset UUIDs
        """
        return [asset_to_add['id'] for asset_to_add in self.assets]

    def get_final_name(self) -> str:
        """ 
        Gets the album model's name to use when talking to Immich, i.e.
        returns override_name if set, otherwise name.
        
        Returns
        ---------
            override_name if set, otherwise name
        """
        if self.override_name:
            return self.override_name
        return self.name


def read_file(file_path: str) -> str:
    """ 
    Reads and returns the contents of the provided file.

    Parameters
    ----------
        file_path : str
            Path to the file to read
    Raises
    ----------
        FileNotFoundError if the file does not exist
        Exception on any other error reading the file
    Returns
    ---------
        The file's contents
    """
    with open(file_path, 'r', encoding="utf-8") as secret_file:
        return secret_file.read().strip()

def read_api_key_from_file(file_path: str) -> str:
    """ 
    Reads the API key from the provided file

    Parameters
    ----------
        file_path : str
            Path to the file to read
    Returns
    ---------
        The API key or None on error
    """
    try:
        return read_file(file_path)
    except FileNotFoundError:
        logging.error("API Key file not found at %s", args["api_key"])
    except OSError as ex:
        logging.error("Error reading API Key file: %s", ex)
    return None

def determine_api_key(api_key_source: str, key_type: str) -> str:
    """ 
    Determines the API key base on key_type.
    For key_type 'literal', api_key_source is returned as is.
    For key'type 'file', api_key_source is a path to a file containing the API key,
    and the file's contents are returned.

    Parameters
    ----------
        api_key_source : str
            An API key or path to a file containing an API key
        key_type : str
            Must be either 'literal' or 'file'
    Returns
    ---------
        The API key or None on error
    """
    if key_type == 'literal':
        return api_key_source
    if key_type == 'file':
        return read_file(api_key_source)
    # At this point key_type is not a valid value
    logging.error("Unknown key type (-t, --key-type). Must be either 'literal' or 'file'.")
    return None

def expand_to_glob(expr: str) -> str:
    """ 
    Expands the passed expression to a glob-style
    expression if it doesn't contain neither a slash nor an asterisk.
    The resulting glob-style expression matches any path that contains the 
    original expression anywhere.

    Parameters
    ----------
        expr : str
            Expression to expand to a GLOB-style expression if not already
            one
    Returns
    ---------
        The original expression if it contained a slash or an asterisk,
        otherwise \\*\\*/\\*\\<expr\\>\\*/\\*\\*
    """
    if not '/' in expr and not '*' in expr:
        glob_expr = f'**/*{expr}*/**'
        logging.debug("expanding %s to %s", expr, glob_expr)
        return glob_expr
    return expr

def divide_chunks(full_list: list, chunk_size: int):
    """Yield successive n-sized chunks from l. """
    # looping till length l
    for j in range(0, len(full_list), chunk_size):
        yield full_list[j:j + chunk_size]

def parse_separated_string(separated_string: str, separator: str) -> Tuple[str, str]:
    """
    Parse a key, value pair, separated by the provided separator.
    
    That's the reverse of ShellArgs.
    On the command line (argparse) a declaration will typically look like:
        foo=hello
    or
        foo="hello world"
    """
    items = separated_string.split(separator)
    key = items[0].strip() # we remove blanks around keys, as is logical
    value = None
    if len(items) > 1:
        # rejoin the rest:
        value = separator.join(items[1:])
    return (key, value)

def fetch_server_version() -> dict:
    """
    Fetches the API version from the immich server.

    If the API endpoint for getting the server version cannot be reached,
    raises HTTPError
    
    Returns
    -------
        Dictionary with keys 
            - major
            - minor
            - patch
    """
    api_endpoint = f'{root_url}server/version'
    r = requests.get(api_endpoint, **requests_kwargs, timeout=api_timeout)
    # The API endpoint changed in Immich v1.118.0, if the new endpoint
    # was not found try the legacy one
    if r.status_code == 404:
        api_endpoint = f'{root_url}server-info/version'
        r = requests.get(api_endpoint, **requests_kwargs, timeout=api_timeout)

    if r.status_code == 200:
        server_version = r.json()
        logging.info("Detected Immich server version %s.%s.%s", server_version['major'], server_version['minor'], server_version['patch'])
    # Any other errors mean communication error with API
    else:
        logging.error("Communication with Immich API failed! Make sure the passed API URL is correct!")
        check_api_response(r)
    return server_version


def sync_library(library_id: str):
    now = datetime.datetime.now()
    r = requests.post(root_url+'libraries/'+library_id+'/scan', **requests_kwargs, timeout=api_timeout)
    r.raise_for_status()
    pass


def fetch_assets(is_not_in_album: bool, find_archived: bool) -> list:
    """
    Fetches assets from the Immich API.

    Uses the /search/meta-data call. Much more efficient than the legacy method
    since this call allows to filter for assets that are not in an album only.
    
    Parameters
    ----------
        is_not_in_album : bool
            Flag indicating whether to fetch only assets that are not part
            of an album or not. If set to False, will find images in albums and 
            not part of albums
        find_archived : bool
            Flag indicating whether to only fetch assets that are archived. If set to False,
            will find archived and unarchived images
    Returns
    ---------
        An array of asset objects
    """

    return fetch_assets_with_options({'isNotInAlbum': is_not_in_album, 'withArchived': find_archived})

def fetch_assets_with_options(search_options: dict) -> list:
    """
    Fetches assets from the Immich API using specific search options.
    The search options directly correspond to the body used for the search API request.
    
    Parameters
    ----------
        search_options: dict
            Dictionary containing options to pass to the search/metadata API endpoint
    Returns
    ---------
        An array of asset objects
    """
    body = search_options
    assets_found = []
    # prepare request body

    # This API call allows a maximum page size of 1000
    number_of_assets_to_fetch_per_request_search = min(1000, number_of_assets_to_fetch_per_request)
    body['size'] = number_of_assets_to_fetch_per_request_search
    # Initial API call, let's fetch our first chunk
    page = 1
    body['page'] = str(page)
    r = requests.post(root_url+'search/metadata', json=body, **requests_kwargs, timeout=api_timeout)
    r.raise_for_status()
    response_json = r.json()
    assets_received = response_json['assets']['items']
    logging.debug("Received %s assets with chunk %s", len(assets_received), page)

    assets_found = assets_found + assets_received
    # If we got a full chunk size back, let's perform subsequent calls until we get less than a full chunk size
    while len(assets_received) == number_of_assets_to_fetch_per_request_search:
        page += 1
        body['page'] = page
        r = requests.post(root_url+'search/metadata', json=body, **requests_kwargs, timeout=api_timeout)
        check_api_response(r)
        response_json = r.json()
        assets_received = response_json['assets']['items']
        logging.debug("Received %s assets with chunk %s", len(assets_received), page)
        assets_found = assets_found + assets_received
    return assets_found


def fetch_albums():
    """Fetches albums from the Immich API"""

    api_endpoint = 'albums'

    r = requests.get(root_url+api_endpoint, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)
    return r.json()

def fetch_album_info(album_id_for_info: str):
    """
    Fetches information about a specific album

    Parameters
    ----------
        album_id_for_info : str
            The ID of the album to fetch information for

    """

    api_endpoint = f'albums/{album_id_for_info}'

    r = requests.get(root_url+api_endpoint, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)
    return r.json()

def delete_album(album_delete: dict):
    """
    Deletes an album identified by album_to_delete['id']
    
    If the album could not be deleted, logs an error.

    Parameters
    ----------
        album_delete : dict
            Dictionary with the following keys:
                - id
                - albumName

    Returns
    ---------
        True if the album was deleted, otherwise False
    """
    api_endpoint = 'albums'

    logging.debug("Deleting Album: Album ID = %s, Album Name = %s", album_delete['id'], album_delete['albumName'])
    r = requests.delete(root_url+api_endpoint+'/'+album_delete['id'], **requests_kwargs, timeout=api_timeout)
    try:
        check_api_response(r)
        return True
    except HTTPError:
        logging.error("Error deleting album %s: %s", album_delete['albumName'], r.reason)
        return False

def create_album(album_name_to_create: str) -> str:
    """
    Creates an album with the provided name and returns the ID of the created album
    

    Parameters
    ----------
        album_name_to_create : str
            Name of the album to create

    Returns
    ---------
        True if the album was deleted, otherwise False
    
    Raises
    ----------
        Exception if the API call failed
    """

    api_endpoint = 'albums'

    data = {
        'albumName': album_name_to_create
    }
    r = requests.post(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

    return r.json()['id']


def add_assets_to_album(assets_add_album_id: str, asset_list: list[str]) -> list[str]:
    """
    Adds the assets IDs provided in assets to the provided albumId.

    If assets if larger than number_of_images_per_request, the list is chunked
    and one API call is performed per chunk.
    Only logs errors and successes.

    Returns 

    Parameters
    ----------
        assets_add_album_id : str
            The ID of the album to add assets to
        asset_list: list[str]
            A list of asset IDs to add to the album

    Returns
    ---------
        The asset UUIDs that were actually added to the album (not respecting assets that were already part of the album)
    """
    api_endpoint = 'albums'

    # Divide our assets into chunks of number_of_images_per_request,
    # So the API can cope
    assets_chunked = list(divide_chunks(asset_list, number_of_images_per_request))
    asset_list_added = []
    for assets_chunk in assets_chunked:
        data = {'ids':assets_chunk}
        r = requests.put(root_url+api_endpoint+f'/{assets_add_album_id}/assets', json=data, **requests_kwargs, timeout=api_timeout)
        check_api_response(r)
        response = r.json()

        for res in response:
            if not res['success']:
                if  res['error'] != 'duplicate':
                    logging.warning("Error adding an asset to an album: %s", res['error'])
            else:
                asset_list_added.append(res['id'])

    return asset_list_added

def fetch_users():
    """Queries and returns all users"""

    api_endpoint = 'users'

    r = requests.get(root_url+api_endpoint, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)
    return r.json()

# Disable pylint for too many branches
# pylint: disable=R0912
def update_album_shared_state(album_to_share: AlbumModel, unshare_users: bool) -> None:
    """
    Makes sure the album is shared with the users set in the model with the correct roles.
    This involves fetching album info from Immich to check if/who the album is shared with and the share roles,
    then either updating the share role, removing the user, or adding the users

    Parameters
    ----------
        album_to_share : AlbumModel
            The album to share, with the expected share_with setting
        unshare_users: bool
            Flag indicating whether to actively unshare albums if shared with a user that is not in the current
            share settings
    Raises
    ----------
        HTTPError if the API call fails
    """
    # Parse and prepare expected share roles
    # List all share users by share role
    share_users_to_roles_expected = {}
    for share_user in album.share_with:
        # Find the user by configured name or email
        share_user_in_immich = find_user_by_name_or_email(share_user['user'], users)
        if not share_user_in_immich:
            logging.warning("User %s to share album %s with does not exist!", share_user['user'], album.get_final_name())
            continue
        share_users_to_roles_expected[share_user_in_immich['id']] = share_user['role']

    # No users to share with and unsharing is disabled?
    if len(share_users_to_roles_expected) == 0 and not unshare_users:
        return

    # Now fetch reality
    album_to_share_info = fetch_album_info(album_to_share.id)
    # Dict mapping a user ID to share role
    album_share_info = {}
    for share_user_actual in album_to_share_info['albumUsers']:
        album_share_info[share_user_actual['user']['id']] = share_user_actual['role']

    # Group share users by share role
    share_roles_to_users_expected = {}
    # Now compare expectation with reality and update
    for user_to_share_with, share_role_expected in share_users_to_roles_expected.items():
        # Case: Album is not share with user
        if user_to_share_with not in album_share_info:
            # Gather all users to share the album with for this role
            if not share_role_expected in share_roles_to_users_expected:
                share_roles_to_users_expected[share_role_expected] = []
            share_roles_to_users_expected[share_role_expected].append(user_to_share_with)

        # Case: Album is shared, but with wrong role
        elif album_share_info[user_to_share_with] != share_role_expected:
            try:
                update_album_share_user_role(album_to_share.id, user_to_share_with, share_role_expected)
                logging.debug("Sharing: Updated share role for user %s in album %s to %s", user_to_share_with, album_to_share.get_final_name(), share_role_expected)
            except HTTPError as ex:
                logging.warning("Sharing: Error updating share role for user %s in album %s to %s", user_to_share_with, album_to_share.get_final_name(), share_role_expected)
                logging.debug("Error: %s", ex)

    # Now check if the album is shared with any users it should not be shared with
    if unshare_users:
        for shared_user in album_share_info:
            if shared_user not in share_users_to_roles_expected:
                try:
                    unshare_album_with_user(album_to_share.id, shared_user)
                    logging.debug("Sharing: User %s removed from album %s", shared_user, album_to_share.get_final_name())
                except HTTPError as ex:
                    logging.warning("Sharing: Error removing user %s from album %s", shared_user, album_to_share.get_final_name())
                    logging.debug("Error: %s", ex)

    # Now share album with all users it is not already shared with
    if len(share_roles_to_users_expected) > 0:
        # Share album for users by role
        for share_role_group, share_users in share_roles_to_users_expected.items():
            # Convert list of user dicts to list of user IDs
            try:
                share_album_with_user_and_role(album_to_share.id, share_users, share_role_group)
                logging.debug("Album %s shared with users IDs %s in role: %s", album_to_share.get_final_name(), share_users, share_role_group)
            except (AssertionError, HTTPError) as ex:
                logging.warning("Error sharing album %s for users %s in role %s", album_to_share.get_final_name(), share_users, share_role_group)
                logging.debug("Album share error: %s", ex)

def unshare_album_with_user(album_id_to_unshare: str, unshare_user_id: str):
    """
    Unshares the provided album with the provided user

    Parameters
    ----------
        album_id_to_unshare : str
            The ID of the album to unshare
        unshare_user_id: str
            The user ID to remove from the album's share list
    Raises
    ----------
        HTTPError if the API call fails
    """
    api_endpoint = f'albums/{album_id_to_unshare}/user/{unshare_user_id}'
    r = requests.delete(root_url+api_endpoint, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

def update_album_share_user_role(album_id_to_share: str, share_user_id: str, share_user_role: str):
    """
    Updates the user's share role for the provided album ID.

    Parameters
    ----------
        album_id_to_share : str
            The ID of the album to share
        share_user_id: str
            The user ID to update the share role for
        share_user_role: str
            The share role to update the user to
    Raises
    ----------
        AssertionError if user_share_role contains an invalid value  
        HTTPError if the API call fails
    """
    api_endpoint = f'albums/{album_id_to_share}/user/{share_user_id}'

    assert share_role in SHARE_ROLES

    data = {
        'role': share_user_role
    }

    r = requests.put(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

def share_album_with_user_and_role(album_id_to_share: str, user_ids_to_share_with: list[str], user_share_role: str):
    """
    Shares the album with the provided album_id with all provided share_user_ids
    using share_role as a role.

    Parameters
    ----------
        album_id_to_share : str
            The ID of the album to share
        user_ids_to_share_with: list[str]
            IDs of users to share the album with
        user_share_role: str
            The share role to use when sharing the album, valid values are
            "viewer" or "editor"
    Raises
    ----------
        AssertionError if user_share_role contains an invalid value  
        HTTPError if the API call fails
    """
    api_endpoint = f'albums/{album_id_to_share}/users'

    assert share_role in SHARE_ROLES

    # build payload
    album_users = []
    for user_id_to_share_with in user_ids_to_share_with:
        share_info = {}
        share_info['role'] = user_share_role
        share_info['userId'] = user_id_to_share_with
        album_users.append(share_info)

    data = {
        'albumUsers': album_users
    }

    r = requests.put(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

def trigger_offline_asset_removal():
    """
    Removes offline assets.

    Takes into account API changes happening between v1.115.0 and v1.116.0.

    Before v1.116.0, offline asset removal was an asynchronous job that could only be
    triggered by an Administrator for a specific library.

    Since v1.116.0, offline assets are no longer displayed in the main timeline but shown in the trash. They automatically
    come back from the trash when they are no longer offline. The only way to delete them is either by emptying the trash
    (along with everything else) or by selectively deleting all offline assets. This is option the script now uses.

    Raises
    ----------
        HTTPException if any API call fails
    """
    if version['major'] == 1 and version ['minor'] < 116:
        trigger_offline_asset_removal_pre_minor_version_116()
    else:
        trigger_offline_asset_removal_since_minor_version_116()

def trigger_offline_asset_removal_since_minor_version_116():
    """
    Synchronously deletes offline assets.

    Uses the searchMetadata endpoint to find all assets marked as offline, then
    issues a delete call for these asset UUIDs.

    Raises
    ----------
        HTTPException if any API call fails
    """
    # Workaround for a bug where isOffline option is not respected:
    # Search all trashed assets and manually filter for offline assets.
    # WARNING! This workaround must NOT be removed to keep compatibility with Immich v1.116.x to at
    # least v1.117.x (reported issue for v1.117.0, might be fixed with v1.118.0)!
    # If removed the assets for users of v1.116.0 - v1.117.x might be deleted completely!!!
    trashed_assets = fetch_assets_with_options({'trashedAfter': '1970-01-01T00:00:00.000Z'})
    #logging.debug("search results: %s", offline_assets)

    offline_assets = [asset for asset in trashed_assets if asset['isOffline']]

    if len(offline_assets) > 0:
        logging.info("Deleting %s offline assets", len(offline_assets))
        logging.debug("Deleting the following offline assets (count: %d): %s", len(offline_assets), [asset['originalPath'] for asset in offline_assets])
        delete_assets(offline_assets, True)
    else:
        logging.info("No offline assets found!")


def delete_assets(assets_to_delete: list, force: bool):
    """
    Deletes the provided assets from Immich.

    Parameters
    ----------
        assets_to_delete : list
            A list of asset objects with key 'id'.
        force: bool
            Force flag to pass to the API call

    Raises
    ----------
        HTTPException if the API call fails
    """

    api_endpoint = 'assets'
    asset_ids_to_delete = [asset['id'] for asset in assets_to_delete]
    data = {
        'force': force,
        'ids': asset_ids_to_delete
    }

    r = requests.delete(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)



def trigger_offline_asset_removal_pre_minor_version_116():
    """
    Triggers Offline Asset Removal Job.
    Only supported in Immich prior v1.116.0.
    Requires the script to run with an Administrator level API key.
    
    Works by fetching all libraries and triggering the Offline Asset Removal job
    one by one.
    
    Raises
    ----------
        HTTPError if the API call fails
    """
    libraries = fetch_libraries()
    for library in libraries:
        trigger_offline_asset_removal_async(library['id'])

def fetch_libraries() -> list[dict]:
    """
    Queries and returns all libraries
    
    Raises
    ----------
        Exception if any API call fails
    """

    api_endpoint = 'libraries'

    r = requests.get(root_url+api_endpoint, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)
    return r.json()

def trigger_offline_asset_removal_async(library_id: str):
    """
    Triggers removal of offline assets in the library identified by libraryId.

    Parameters
    ----------
        library_id : str
            The ID of the library to trigger offline asset removal for
    Raises
    ----------
        Exception if any API call fails
    """

    api_endpoint = f'libraries/{library_id}/removeOffline'

    r = requests.post(root_url+api_endpoint, **requests_kwargs, timeout=api_timeout)
    if r.status_code == 403:
        logging.fatal("--sync-mode 2 requires an Admin User API key!")
    else:
        check_api_response(r)

def set_album_thumb(thumbnail_album_id: str, thumbnail_asset_id: str):
    """
    Sets asset as thumbnail of album

    Parameters
    ----------
        thumbnail_album_id : str
            The ID of the album for which to set the thumbnail
        thumbnail_asset_id : str
            The ID of the asset to be set as thumbnail
            
    Raises
    ----------
        Exception if the API call fails
    """
    api_endpoint = f'albums/{thumbnail_album_id}'

    data = {"albumThumbnailAssetId": thumbnail_asset_id}

    r = requests.patch(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

def choose_thumbnail(thumbnail_setting: str, thumbnail_asset_list: list[dict]) -> str:
    """
    Tries to find an asset to use as thumbnail depending on thumbnail_setting.
    
    Parameters
    ----------
        thumbnail_setting : str
            Either a fully qualified asset path or one of 'first', 'last', 'random', 'random-filtered'
        asset_list: list[dict]
            A list of assets to choose a thumbnail from, based on thumbnail_setting
            
    Returns
    ----------
        An Immich asset dict or None if no thumbnail was found based on thumbnail_setting
    """
    # Case: fully qualified path
    if thumbnail_setting not in ALBUM_THUMBNAIL_SETTINGS_GLOBAL:
        for asset in thumbnail_asset_list:
            if asset['originalPath'] == thumbnail_setting:
                return asset
        # at this point we could not find the thumbnail asset by path
        return None

    # Case: Anything but fully qualified path
    # Apply filtering to assets
    thumbnail_assets = thumbnail_asset_list

    if len(thumbnail_assets) > 0:
        # Sort assets by creation date
        thumbnail_assets.sort(key=lambda x: x['fileCreatedAt'])
        if thumbnail_setting not in ALBUM_THUMBNAIL_STATIC_INDICES:
            idx = random.randint(0, len(thumbnail_assets)-1)
        else:
            idx = ALBUM_THUMBNAIL_STATIC_INDICES[thumbnail_setting]
        return thumbnail_assets[idx]

    # Case: Invalid thumbnail_setting
    return None


def update_album_properties(album_to_update: AlbumModel):
    """
    Sets album properties in Immich to the properties of the AlbumModel

    Parameters
    ----------
        album_to_update : AlbumModel
            The album model to use for updating the album
            
    Raises
    ----------
        Exception if the API call fails
    """
    # Initialize payload
    data = {}

    # Handle thumbnail
    # Thumbnail setting 'random-all' is handled separately
    if album_to_update.thumbnail_setting and album_to_update.thumbnail_setting != ALBUM_THUMBNAIL_RANDOM_ALL:
        # Fetch assets to be sure to have up-to-date asset list
        album_to_update_info = fetch_album_info(album_to_update.id)
        album_assets = album_to_update_info['assets']
        thumbnail_asset = choose_thumbnail(album_to_update.thumbnail_setting, album_assets)
        if thumbnail_asset:
            logging.info("Using asset %s as thumbnail for album %s", thumbnail_asset['originalPath'], album_to_update.get_final_name())
            data['albumThumbnailAssetId'] = thumbnail_asset['id']
        else:
            logging.warning("Unable to determine thumbnail for setting '%s' in album %s", album.thumbnail_setting, album.get_final_name())

    # Description
    if album_to_update.description:
        data['description'] = album.description

    # Sorting Order
    if album_to_update.sort_order:
        data['order'] = album.sort_order

    # Comments / Likes enabled
    if album_to_update.comments_and_likes_enabled is not None:
        data['isActivityEnabled'] = album_to_update.comments_and_likes_enabled

    # Only update album if there is something to update
    if len(data) > 0:
        api_endpoint = f'albums/{album_to_update.id}'

        response = requests.patch(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
        check_api_response(response)

def set_assets_archived(asset_ids_to_archive: list[str], is_archived: bool):
    """
    (Un-)Archives the assets identified by the passed list of UUIDs.

    Parameters
    ----------
        asset_ids_to_archive : list
            A list of asset IDs to archive
        isArchived : bool
            Flag indicating whether to archive or unarchive the passed assets
   
    Raises
    ----------
        Exception if the API call fails
    """
    api_endpoint = 'assets'

    data = {
        "ids": asset_ids_to_archive,
        "isArchived": is_archived
    }

    r = requests.put(root_url+api_endpoint, json=data, **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

def check_api_response(response: requests.Response):
    """
    Checks the HTTP return code for the provided response and
    logs any errors before raising an HTTPError

    Parameters
    ----------
        response : requests.Response
            A list of asset IDs to archive
        isArchived : bool
            Flag indicating whether to archive or unarchive the passed assets
   
    Raises
    ----------
        HTTPError if the API call fails
    """
    try:
        response.raise_for_status()
    except HTTPError:
        if response.json():
            logging.error("Error in API call: %s", response.json())
        else:
            logging.error("API response did not contain a payload")
    response.raise_for_status()

def set_album_properties_in_model(album_model_to_update: AlbumModel):
    """
    Sets the album_model's properties based on script options set.
    
    Parameters
    ----------
        album_model : AlbumModel
            The album model to set the properties for
    """
    # Set share_with
    if share_with:
        for album_share_user in share_with:
            # Resolve share user-specific share role syntax <name>=<role>
            share_user_name, share_user_role = parse_separated_string(album_share_user, '=')
            # Fallback to default
            if share_user_role is None:
                share_user_role = share_role

            album_share_with = {
                'user': share_user_name,
                'role': share_user_role
            }
            album_model_to_update.share_with.append(album_share_with)

    # Thumbnail Setting
    if set_album_thumbnail:
        album_model_to_update.thumbnail_setting = set_album_thumbnail

    # Archive setting
    if archive:
        album_model_to_update.archive = archive

    # Sort Order
    if album_order:
        album_model_to_update.sort_order = album_order

    # Comments and Likes
    if comments_and_likes_enabled:
        album_model_to_update.comments_and_likes_enabled = True
    elif comments_and_likes_disabled:
        album_model_to_update.comments_and_likes_enabled = False

def build_id_mapping(asset_list : list[dict], local_root_path : str, immich_root_path : str) -> dict:
    asset_by_local_path = dict(
            (local_root_path + asset['originalPath'][len(immich_root_path):], asset)
            for asset in asset_list
            if asset['originalPath'].startswith(immich_root_path)
        )
    with sqlite3.connect('file:' + os.path.join(local_root_path, 'database.sqlite3') + '?mode=ro', uri=True) as db:
        cursor = db.cursor()
        asset_by_gpid = {}
        for row in cursor.execute('SELECT uuid, path FROM media'):
            path = os.path.normpath(row[1])
            asset = asset_by_local_path.get(path)
            if asset is not None:
                asset_by_gpid[row[0]] = asset
            else:
                logging.debug("Cannot map: %s", path)
    return asset_by_gpid

def build_album_list(asset_by_gpid : dict, local_root_path : str) -> dict:
    """
    Builds a list of album models, enriched with assets assigned to each album.
    Returns a dict where the key is the album name and the value is the model.
    Attention!
    """
    album_ids = set()
    album_asset_ids = defaultdict(set)
    album_models = defaultdict(list)

    debug_path = os.path.join(local_root_path, 'debug')
    google_albums = json.load(open(os.path.join(debug_path, 'album_list.json'), 'r')) + \
            json.load(open(os.path.join(debug_path, 'shared_album_list.json'), 'r'))
    for google_album in google_albums:
        if 'mediaItemsCount' not in google_album or 'title' not in google_album:
            continue
        album_name = google_album['title']
        album_id = google_album['id']
        if album_id in album_ids:
            continue
        album_ids.add(album_id)

        if album_name not in album_models:
            new_album_model = AlbumModel(album_name)
            thumbnail_id = google_album.get('coverPhotoMediaItemId')
            if thumbnail_id is not None:
                thumbnail_asset = asset_by_gpid.get(thumbnail_id)
                if thumbnail_asset is not None:
                    new_album_model.thumbnail_setting = thumbnail_asset['originalPath']
            set_album_properties_in_model(new_album_model)
        else:
            new_album_model = album_models[album_name]
        asset_ids = album_asset_ids[album_name]

        google_assets = json.load(open(os.path.join(debug_path, f'album-{album_id}.json'), 'r'))
        for google_asset in google_assets:
            asset_id = google_asset['id']
            if asset_id in asset_ids:
                continue
            asset_ids.add(asset_id)
            asset = asset_by_gpid.get(asset_id)
            if asset is None:
                logging.debug("Cannot find media: %s", asset_id)
            else:
                new_album_model.assets.append(asset)

        album_models[new_album_model.get_final_name()] = new_album_model

    return album_models

def find_user_by_name_or_email(name_or_email: str, user_list: list[dict]) -> dict:
    """
    Finds a user identified by name_or_email in the provided user_list.

    Parameters
    ----------
        name_or_email: str
            The user name or email address to find the user by
        user_list: list[dict]
            A list of user dictionaries with the following mandatory keys:
              - id
              - name
              - email
    Returns
    ---------
        A user dict with matching name or email or None if no matching user was found
    """
    for user in user_list:
        # Search by name or mail address
        if name_or_email in (user['name'], user['email']):
            return user
    return None

parser = argparse.ArgumentParser(description="Create Immich Albums from an external library path based on the top level folders",
    formatter_class=argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument("local_root_path", help="The external library's root path locally")
parser.add_argument("immich_root_path", help="The external library's root path in Immich")
parser.add_argument("api_url", help="The root API URL of immich, e.g. https://immich.mydomain.com/api/")
parser.add_argument("api_key", help="The Immich API Key to use. Set --api-key-type to 'file' if a file path is provided.")
parser.add_argument("-t", "--api-key-type", default="literal", choices=['literal', 'file'], help="The type of the Immich API Key")
parser.add_argument("-u", "--unattended", action="store_true", help="Do not ask for user confirmation after identifying albums. Set this flag to run script as a cronjob.")
parser.add_argument("-c", "--chunk-size", default=2000, type=int, help="Maximum number of assets to add to an album with a single API call")
parser.add_argument("-C", "--fetch-chunk-size", default=5000, type=int, help="Maximum number of assets to fetch with a single API call")
parser.add_argument("-l", "--log-level", default="INFO", choices=['CRITICAL', 'ERROR', 'WARNING', 'INFO', 'DEBUG'], help="Log level to use")
parser.add_argument("-k", "--insecure", action="store_true", help="Pass to ignore SSL verification")
parser.add_argument("-x", "--share-with", action="append",
                    help="""A user name (or email address of an existing user) to share newly created albums with.
                    Sharing only happens if the album was actually created, not if new assets were added to an existing album.
                    If the the share role should be specified by user, the format <userName>=<shareRole> must be used, where <shareRole> must be one of 'viewer' or 'editor'.
                    May be specified multiple times to share albums with more than one user.""")
parser.add_argument("-o", "--share-role", default="viewer", choices=['viewer', 'editor'],
                    help="""The default share role for users newly created albums are shared with.
                            Only effective if --share-with is specified at least once and the share role is not specified within --share-with.""")
parser.add_argument("-S", "--sync-mode", default=0, type=int, choices=[0, 1, 2],
                    help="""Synchronization mode to use. Synchronization mode helps synchronizing changes in external libraries structures to Immich after albums
                            have already been created. Possible Modes: 0 = do nothing; 1 = Delete any empty albums; 2 = Delete offline assets AND any empty albums""")
parser.add_argument("-O", "--album-order", default=False, type=str, choices=[False, 'asc', 'desc'],
                    help="Set sorting order for newly created albums to newest or oldest file first, Immich defaults to newest file first")
parser.add_argument("-A", "--find-assets-in-albums", action="store_true",
                    help="""By default, the script only finds assets that are not assigned to any album yet.
                            Set this option to make the script discover assets that are already part of an album and handle them as usual.
                            If --find-archived-assets is set as well, both options apply.""")
parser.add_argument("--set-album-thumbnail", choices=ALBUM_THUMBNAIL_SETTINGS_GLOBAL,
                    help="""Set first/last/random image as thumbnail for newly created albums or albums assets have been added to.
                            If set to """+ALBUM_THUMBNAIL_RANDOM_ALL+""", the thumbnails for ALL albums will be shuffled on every run.""")
parser.add_argument("-v", "--archive", action="store_true",
                    help="""Set this option to automatically archive all assets that were newly added to albums.
                            If this option is set in combination with --mode = CLEANUP or DELETE_ALL, archived images of deleted albums will be unarchived.
                            Archiving hides the assets from Immich's timeline.""")
parser.add_argument("--find-archived-assets", action="store_true",
                    help="""By default, the script only finds assets that are not archived in Immich.
                            Set this option to make the script discover assets that are already archived.
                            If -A/--find-assets-in-albums is set as well, both options apply.""")
parser.add_argument("--read-album-properties", action="store_true",
                    help="""If set, the script tries to access all passed root paths and recursively search for .albumprops files in all contained folders.
                            These properties will be used to set custom options on an per-album level. Check the readme for a complete documentation.""")
parser.add_argument("--api-timeout",  default=REQUEST_TIMEOUT_DEFAULT, type=int, help="Timeout when requesting Immich API in seconds")
parser.add_argument("--comments-and-likes-enabled", action="store_true",
                    help="Pass this argument to enable comment and like functionality in all albums this script adds assets to. Cannot be used together with --comments-and-likes-disabled")
parser.add_argument("--comments-and-likes-disabled", action="store_true",
                    help="Pass this argument to disable comment and like functionality in all albums this script adds assets to. Cannot be used together with --comments-and-likes-enabled")
parser.add_argument("--update-album-props-mode", type=int, choices=[0, 1, 2], default=0,
                    help="""Change how album properties are updated whenever new assets are added to an album. Album properties can either come from script arguments or the .albumprops file.
                            Possible values:
                            0 = Do not change album properties.
                            1 = Only override album properties but do not change the share status.
                            2 = Override album properties and share status, this will remove all users from the album which are not in the SHARE_WITH list.""")
parser.add_argument("--sync-library", type=str, metavar="LIBRARY_ID",
                    help="Sync the selected library before starting the main action")


args = vars(parser.parse_args())
# set up logger to log in logfmt format
logging.basicConfig(level=args["log_level"], stream=sys.stdout, format='time=%(asctime)s level=%(levelname)s msg=%(message)s')
logging.Formatter.formatTime = (lambda self, record, datefmt=None: datetime.datetime.fromtimestamp(record.created, datetime.timezone.utc).astimezone().isoformat(sep="T",timespec="milliseconds"))

local_root_path = args["local_root_path"]
immich_root_path = args["immich_root_path"]
root_url = args["api_url"]
api_key = determine_api_key(args["api_key"], args["api_key_type"])
if api_key is None:
    logging.fatal("Unable to determine API key with API Key type %s", args["api_key_type"])
    sys.exit(1)
number_of_images_per_request = args["chunk_size"]
number_of_assets_to_fetch_per_request = args["fetch_chunk_size"]
unattended = args["unattended"]
album_order = args["album_order"]
insecure = args["insecure"]
share_with = args["share_with"]
share_role = args["share_role"]
sync_mode = args["sync_mode"]
find_assets_in_albums = args["find_assets_in_albums"]
set_album_thumbnail = args["set_album_thumbnail"]
archive = args["archive"]
find_archived_assets = args["find_archived_assets"]
read_album_properties = args["read_album_properties"]
api_timeout = args["api_timeout"]
comments_and_likes_enabled = args["comments_and_likes_enabled"]
comments_and_likes_disabled = args["comments_and_likes_disabled"]
if comments_and_likes_disabled and comments_and_likes_enabled:
    logging.fatal("Arguments --comments-and-likes-enabled and --comments-and-likes-disabled cannot be used together! Choose one!")
    sys.exit(1)
update_album_props_mode = args["update_album_props_mode"]
library_to_sync = args["sync_library"]

is_docker = os.environ.get(ENV_IS_DOCKER, False)

logging.debug("local_root_path = %s", local_root_path)
logging.debug("immich_root_path = %s", immich_root_path)
logging.debug("root_url = %s", root_url)
logging.debug("api_key = %s", api_key)
logging.debug("number_of_images_per_request = %d", number_of_images_per_request)
logging.debug("number_of_assets_to_fetch_per_request = %d", number_of_assets_to_fetch_per_request)
logging.debug("unattended = %s", unattended)
logging.debug("album_order = %s", album_order)
logging.debug("insecure = %s", insecure)
logging.debug("is_docker = %s", is_docker)
logging.debug("share_with = %s", share_with)
logging.debug("share_role = %s", share_role)
logging.debug("sync_mode = %d", sync_mode)
logging.debug("find_assets_in_albums = %s", find_assets_in_albums)
logging.debug("set_album_thumbnail = %s", set_album_thumbnail)
logging.debug("archive = %s", archive)
logging.debug("find_archived_assets = %s", find_archived_assets)
logging.debug("read_album_properties = %s", read_album_properties)
logging.debug("api_timeout = %s", api_timeout)
logging.debug("comments_and_likes_enabled = %s", comments_and_likes_enabled)
logging.debug("comments_and_likes_disabled = %s", comments_and_likes_disabled)
logging.debug("update_album_props_mode = %d", update_album_props_mode)
logging.debug("library_to_sync = %d", library_to_sync)

# Request arguments for API calls
requests_kwargs = {
    'headers' : {
        'x-api-key': api_key,
        'Content-Type': 'application/json',
        'Accept': 'application/json'
    },
    'verify' : not insecure
}

if insecure:
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# append trailing slash to all root paths
# pylint: disable=C0200
if local_root_path[-1] != '/':
    local_root_path = local_root_path + '/'
if immich_root_path[-1] != '/':
    immich_root_path = immich_root_path + '/'
# append trailing slash to root URL
if root_url[-1] != '/':
    root_url = root_url + '/'

version = fetch_server_version()
# Check version
if version['major'] == 1 and version ['minor'] < 106:
    logging.fatal("This script only works with Immich Server v1.106.0 and newer! Update Immich Server or use script version 0.8.1!")
    sys.exit(1)

if library_to_sync is not None:
    sync_library(library_to_sync)

album_properties_templates = {}
if read_album_properties:
    logging.debug("Albumprops: Finding, parsing and merging %s files", ALBUMPROPS_FILE_NAME)
    album_properties_templates = build_album_properties_templates()
    for album_properties_path, album_properties_template in album_properties_templates.items():
        logging.debug("Albumprops: %s -> %s", album_properties_path, album_properties_template)

logging.info("Requesting all assets")
assets = fetch_assets(not find_assets_in_albums, find_archived_assets)
logging.info("%d photos found", len(assets))

logging.info("Mapping Google Photos IDs to Immich assets")
asset_by_gpid = build_id_mapping(assets, local_root_path, immich_root_path)
logging.info("%d photos mapped", len(asset_by_gpid))

logging.info("Sorting assets to corresponding albums using Google Photos archiver debug metadata")
albums_to_create = build_album_list(asset_by_gpid, local_root_path)
albums_to_create = dict(sorted(albums_to_create.items(), key=lambda item: item[0]))

logging.info("%d albums identified", len(albums_to_create))
logging.info("Album list: %s", list(albums_to_create.keys()))

if not unattended:
    if is_docker:
        print("Check that this is the list of albums you want to create. Run the container with environment variable UNATTENDED set to 1 to actually create these albums.")
        sys.exit(0)
    else:
        print("Press enter to create these albums, Ctrl+C to abort")
        input()

logging.info("Listing existing albums on immich")

albums = fetch_albums()
album_to_id = {album['albumName']:album['id'] for album in albums }
logging.info("%d existing albums identified", len(albums))
# Set album ID for existing albums
for album in albums_to_create.values():
    if album.get_final_name() in album_to_id:
        # Album already exists, just get the ID
        album.id = album_to_id[album.get_final_name()]

# Get all users in preparation for album sharing
users = fetch_users()
logging.debug("Found users: %s", users)

# mode CREATE
logging.info("Creating albums if needed")
created_albums = []
# List for gathering all asset UUIDs for later archiving
asset_uuids_added = []
for album in albums_to_create.values():
    if not album.get_final_name() in album_to_id:
        # Create album
        album.id = create_album(album.get_final_name())
        album_to_id[album.get_final_name()] = album.id
        created_albums.append(album)
        logging.info('Album %s added!', album.get_final_name())
    else:
        album.id = album_to_id[album.get_final_name()]

    logging.info("Adding assets to album %s", album.get_final_name())
    assets_added = add_assets_to_album(album.id, album.get_asset_uuids())
    if len(assets_added) > 0:
        asset_uuids_added += assets_added
        logging.info("%d new assets added to %s", len(assets_added), album.get_final_name())

    # Update album properties depending on mode or if newly created
    if update_album_props_mode > 0 or (album in created_albums):
        # Update album properties
        try:
            update_album_properties(album)
        except HTTPError as e:
            logging.error('Error updating properties for album %s: %s', album.get_final_name(), e)

    # Update album sharing if needed or newly created
    if update_album_props_mode == 2 or (album in created_albums):
        # Handle album sharing
        update_album_shared_state(album, True)

logging.info("%d albums created", len(created_albums))

# Archive assets
if archive and len(asset_uuids_added) > 0:
    set_assets_archived(asset_uuids_added, True)
    logging.info("Archived %d assets", len(asset_uuids_added))

# Perform album cover randomization
if set_album_thumbnail == ALBUM_THUMBNAIL_RANDOM_ALL:
    logging.info("Picking a new random thumbnail for all albums")
    albums = fetch_albums()
    for album in albums:
        album_info = fetch_album_info(album['id'])
        # Create album model for thumbnail randomization
        album_model = AlbumModel(album['albumName'])
        album_model.id = album['id']
        album_model.assets = album_info['assets']
        # Set thumbnail setting to 'random' in model
        album_model.thumbnail_setting = 'random'
        # Update album properties (which will only pick a random thumbnail and set it, no other properties are changed)
        update_album_properties(album_model)


# Perform sync mode action: Trigger offline asset removal
if sync_mode == 2:
    logging.info("Trigger offline asset removal")
    trigger_offline_asset_removal()

# Perform sync mode action: Delete empty albums
#
# For Immich versions prior to v1.116.0:
# Attention: Since Offline Asset Removal is an asynchronous job,
# albums affected by it are most likely not empty yet! So this
# might only be effective in the next script run.
if sync_mode >= 1:
    logging.info("Deleting all empty albums")
    albums = fetch_albums()
    # pylint: disable=C0103
    empty_album_count = 0
    # pylint: disable=C0103
    cleaned_album_count = 0
    for album in albums:
        if album['assetCount'] == 0:
            empty_album_count += 1
            logging.info("Deleting empty album %s", album['albumName'])
            if delete_album(album):
                cleaned_album_count += 1
    if empty_album_count > 0:
        logging.info("Successfully deleted %d/%d empty albums!", cleaned_album_count, empty_album_count)
    else:
        logging.info("No empty albums found!")

logging.info("Done!")
