#!/usr/bin/env python3
"""Offline checks for identity repair without changing real GitHub credentials."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


SCRIPT = Path(__file__).with_name('check-github.sh')
MOCK = '''
import json, os, pathlib, sys
args = sys.argv[1:]
with open(os.environ['SEXTICS_AUTH_TEST_CALLS'], 'a') as log:
    log.write(json.dumps(args) + '\\n')
state = pathlib.Path(os.environ['SEXTICS_AUTH_TEST_STATE'])
if args[:1] == ['api'] and args[3] == 'user':
    identity = 'fqlx' if state.exists() else os.environ['SEXTICS_AUTH_TEST_LOGIN']
    if not identity:
        sys.exit(1)
    print(identity)
elif args[:1] == ['api'] and args[3].startswith('repos/'):
    print(os.environ.get('SEXTICS_AUTH_TEST_PUSH', 'true'))
elif args[:2] == ['auth', 'status']:
    print(os.environ.get('SEXTICS_AUTH_TEST_STORED', ''))
elif args[:2] == ['auth', 'switch']:
    state.touch()
else:
    sys.exit('Unexpected gh mutation or command')
'''


class GithubAuthentication(unittest.TestCase):
    def run_check(self, login, *arguments, token=None, stored='', push='true', git_helper=''):
        with tempfile.TemporaryDirectory(prefix='sextics-auth-test-') as directory:
            fixture = Path(directory)
            binary = fixture / 'gh'
            binary.write_text(f'#!{sys.executable}\n' + MOCK)
            binary.chmod(0o755)
            git = fixture / 'git'
            git.write_text(f'#!{sys.executable}\n'
                           'import os, sys\n'
                           "helper = os.environ.get('SEXTICS_AUTH_TEST_GIT_HELPER', '')\n"
                           'if helper: print(helper)\n'
                           'sys.exit(0 if helper else 1)\n')
            git.chmod(0o755)
            environment = dict(os.environ)
            for name in ('GH_TOKEN', 'GITHUB_TOKEN'):
                environment.pop(name, None)
            environment.update({
                'PATH': str(fixture) + os.pathsep + environment['PATH'],
                'SEXTICS_AUTH_TEST_CALLS': str(fixture / 'calls.jsonl'),
                'SEXTICS_AUTH_TEST_STATE': str(fixture / 'switched'),
                'SEXTICS_AUTH_TEST_LOGIN': login,
                'SEXTICS_AUTH_TEST_STORED': stored,
                'SEXTICS_AUTH_TEST_PUSH': push,
                'SEXTICS_AUTH_TEST_GIT_HELPER': git_helper,
            })
            if token is not None:
                environment['GH_TOKEN'] = token
            result = subprocess.run(['bash', str(SCRIPT), *arguments],
                                    env=environment, capture_output=True, text=True)
            log = fixture / 'calls.jsonl'
            self.assertTrue(log.is_file(), result.stderr)
            calls = [json.loads(line) for line in log.read_text().splitlines()]
            self.assertFalse(any('setup-git' in command for command in calls))
            if token:
                self.assertNotIn(token, result.stdout + result.stderr)
            return result, calls

    def test_fqlx_identity_and_permission(self):
        result, calls = self.run_check('fqlx')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 2)

    def test_wrong_environment_identity_is_not_bypassed(self):
        result, calls = self.run_check('someone-else', '--repair-stored-account',
                                      token='test-only-placeholder', stored='fqlx')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 1)
        self.assertIn('Cannot switch an environment-token identity', result.stderr)

    def test_invalid_environment_token_is_not_bypassed(self):
        result, calls = self.run_check('', '--repair-stored-account',
                                      token='test-only-placeholder', stored='fqlx')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(len(calls), 1)

    def test_stored_fqlx_can_be_selected_and_rechecked(self):
        result, calls = self.run_check('someone-else', '--repair-stored-account', stored='fqlx')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(sum(command[:2] == ['auth', 'switch'] for command in calls), 1)
        self.assertEqual(sum(command[:1] == ['api'] and command[3] == 'user'
                             for command in calls), 2)

    def test_absent_stored_account_is_not_created(self):
        result, calls = self.run_check('', '--repair-stored-account')
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(any(command[:2] == ['auth', 'switch'] for command in calls))

    def test_gh_git_credential_helper_prevents_account_switch(self):
        result, calls = self.run_check('someone-else', '--repair-stored-account',
                                      stored='fqlx',
                                      git_helper='credential.https://github.com.helper !gh auth git-credential')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('Git uses gh as a credential helper', result.stderr)
        self.assertFalse(any(command[:2] == ['auth', 'switch'] for command in calls))

    def test_push_permission_is_required(self):
        result, _ = self.run_check('fqlx', push='false')
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('push permission', result.stderr)


if __name__ == '__main__':
    unittest.main(verbosity=2)
