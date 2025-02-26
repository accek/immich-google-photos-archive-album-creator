
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
import time
from urllib.error import HTTPError

import urllib3
import requests

# Environment variable to check if the script is running inside Docker
ENV_IS_DOCKER = "IS_DOCKER"

# Immich API request timeout
REQUEST_TIMEOUT_DEFAULT = 20


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


def sync_library(library_id: str, wait: bool) -> None:
    request_time = datetime.datetime.now(datetime.UTC)
    r = requests.post(root_url+'libraries/'+library_id+'/scan', **requests_kwargs, timeout=api_timeout)
    check_api_response(r)

    if wait:
        while True:
            time.sleep(1)
            r = requests.get(root_url+'libraries/'+library_id, **requests_kwargs, timeout=api_timeout)
            check_api_response(r)
            refreshed_at = datetime.datetime.fromisoformat(r.json()["refreshedAt"])
            if refreshed_at > request_time:
                break

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


parser = argparse.ArgumentParser(description="Sync Immich External Library",
    formatter_class=argparse.ArgumentDefaultsHelpFormatter)
parser.add_argument("library_id", help="The external library ID")
parser.add_argument("api_url", help="The root API URL of immich, e.g. https://immich.mydomain.com/api/")
parser.add_argument("api_key", help="The Immich API Key to use. Set --api-key-type to 'file' if a file path is provided.")
parser.add_argument("-t", "--api-key-type", default="literal", choices=['literal', 'file'], help="The type of the Immich API Key")
parser.add_argument("-l", "--log-level", default="INFO", choices=['CRITICAL', 'ERROR', 'WARNING', 'INFO', 'DEBUG'], help="Log level to use")
parser.add_argument("-k", "--insecure", action="store_true", help="Pass to ignore SSL verification")
parser.add_argument("--api-timeout",  default=REQUEST_TIMEOUT_DEFAULT, type=int, help="Timeout when requesting Immich API in seconds")
parser.add_argument("-w", "--wait", action="store_true",
                    help="Wait for the operation to complete")


args = vars(parser.parse_args())
# set up logger to log in logfmt format
logging.basicConfig(level=args["log_level"], stream=sys.stdout, format='time=%(asctime)s level=%(levelname)s msg=%(message)s')
logging.Formatter.formatTime = (lambda self, record, datefmt=None: datetime.datetime.fromtimestamp(record.created, datetime.timezone.utc).astimezone().isoformat(sep="T",timespec="milliseconds"))

library_id = args["library_id"]
root_url = args["api_url"]
api_key = determine_api_key(args["api_key"], args["api_key_type"])
if api_key is None:
    logging.fatal("Unable to determine API key with API Key type %s", args["api_key_type"])
    sys.exit(1)
insecure = args["insecure"]
api_timeout = args["api_timeout"]
wait = args["wait"]

is_docker = os.environ.get(ENV_IS_DOCKER, False)

logging.debug("library_id = %s", library_id)
logging.debug("root_url = %s", root_url)
logging.debug("api_key = %s", api_key)
logging.debug("insecure = %s", insecure)
logging.debug("is_docker = %s", is_docker)
logging.debug("wait = %s", wait)

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

# append trailing slash to root URL
if root_url[-1] != '/':
    root_url = root_url + '/'

version = fetch_server_version()
# Check version
if version['major'] == 1 and version ['minor'] < 106:
    logging.fatal("This script only works with Immich Server v1.106.0 and newer! Update Immich Server or use script version 0.8.1!")
    sys.exit(1)

sync_library(library_id, wait)
logging.info("Done!")
