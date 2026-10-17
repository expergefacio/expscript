#!/usr/bin/env python3
r"""

    getsubs - download up to 3 English and 2 Norwegian subtitles per video.

    install is a bit messy, but here would be how to do it:

    Install (Ubuntu/Debian):
    
sudo apt install pipx ffmpeg libmediainfo0 curl
pipx ensurepath
pipx install 'subliminal==2.8.0'
pipx inject subliminal 'ffsubsync==0.5.1'

    Config (fill in your usernames and passwords):
    
mkdir -p "$HOME/.config/subliminal"
cat > "$HOME/.config/subliminal/subliminal.toml" <<'TOML'
[download]
provider = ["opensubtitlescom", "addic7ed", "gestdown"]
refiner = ["hash", "metadata"]
[provider.opensubtitlescom]
username = "YOUR_OPENSUBTITLES_USERNAME"
password = 'YOUR_OPENSUBTITLES_PASSWORD'
[provider.addic7ed]
username = "YOUR_ADDIC7ED_USERNAME"
password = 'YOUR_ADDIC7ED_PASSWORD'
TOML
chmod 600 "$HOME/.config/subliminal/subliminal.toml"

    Download:
    
curl -fL 'https://raw.githubusercontent.com/expergefacio/expscript/main/subliminial_top5.py' -o "$HOME/subliminal_top5.py"
    OR use wget instead:
wget -O "$HOME/subliminal_top5.py" 'https://raw.githubusercontent.com/expergefacio/expscript/main/subliminial_top5.py'

    Shell setup - copy ONE of the following blocks.

    zsh:
    
cat >> "$HOME/.zshrc" <<'GETSUBS'
getsubs() {
  "$HOME/.local/share/pipx/venvs/subliminal/bin/python" \
    "$HOME/subliminal_top5.py" "$@"
}
GETSUBS
. "$HOME/.zshrc"

    bash:
    
cat >> "$HOME/.bashrc" <<'GETSUBS'
getsubs() {
  "$HOME/.local/share/pipx/venvs/subliminal/bin/python" \
    "$HOME/subliminal_top5.py" "$@"
}
GETSUBS
. "$HOME/.bashrc"

    sh (login shell):
    
cat >> "$HOME/.profile" <<'GETSUBS'
getsubs() {
  "$HOME/.local/share/pipx/venvs/subliminal/bin/python" \
    "$HOME/subliminal_top5.py" "$@"
}
GETSUBS
. "$HOME/.profile"

    How it works:
    Prefers file-hash matches; otherwise uses matching film/episode subtitles and
    synchronizes them to the video's audio with ffsubsync. Saves beside the video
    as Movie.en.1.srt, Movie.en.2.srt, Movie.no.1.srt, etc. Timing can need checking.
    Existing media and subtitles are preserved. An exact-name Movie.srt with at
    least 50 line breaks is also copied to Movie.en.0.default.srt (English assumed).
    A hidden per-video .sublime_finished.json records attempts so folder scans skip
    previously processed videos. Matching/sync policy updates retry missing slots
    once. Stops when OpenSubtitles' allowance runs out; rerun after it resets.

    Commands:
    
getsubs
    Scan the current folder and all subfolders for video files.

getsubs "videofile.mkv"
    Process one video, retrying missing alternatives from earlier attempts.

getsubs > log.log 2>&1
    Scan and write all output to a log.
"""



from __future__ import annotations

import argparse
import copy
import hashlib
import json
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unicodedata
from contextlib import contextmanager
from dataclasses import dataclass
from collections import Counter
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from functools import wraps
from pathlib import Path
from types import SimpleNamespace
from urllib.parse import urlsplit

try:
    import tomlkit
    from babelfish import Language
    from platformdirs import user_config_path
    from subliminal import (
        VIDEO_EXTENSIONS, Episode, Movie, ProviderPool, compute_score, get_scores,
        provider_manager, refine, refiner_manager, region, scan_video,
    )
    from subliminal.matches import fps_matches
    from subliminal.core import scan_name
    from subliminal.exceptions import DownloadLimitExceeded
    from subliminal.providers.opensubtitlescom import DownloadLimitReached
    from subliminal.subtitle import filter_and_sort_categories
except ImportError:
    raise SystemExit(
        'Run this script with the Python interpreter inside Subliminal\'s pipx environment:\n'
        '~/.local/share/pipx/venvs/subliminal/bin/python subliminal-top5.py --help'
    ) from None


MEDIA_EXTENSIONS = frozenset(VIDEO_EXTENSIONS) | {
    '.264', '.265', '.amv', '.av1', '.avc', '.braw', '.cine',
    '.crm', '.drc', '.f4p', '.f4v', '.h265', '.hevc', '.ismv',
    '.ivf', '.j2v', '.m1s', '.m2t', '.m2p', '.m2ps', '.m4p', '.m4s',
    '.mjpg', '.mj2', '.mod', '.mp2v', '.mp4v', '.mp21', '.mpeg1', '.mpeg2',
    '.mpeg4', '.mpv4', '.mts', '.mve', '.nuv', '.ogx', '.prores', '.r3d',
    '.rcv', '.rec', '.rmhd', '.svi', '.ssif', '.tod', '.tp', '.trp', '.tts',
    '.vc1', '.vp6', '.vp8', '.vp9', '.wtv', '.x265', '.y4m', '.yuv',
}
LANGUAGES = {
    'en': {Language('eng')},
    'no': {Language('nor'), Language('nob'), Language('nno')},
}
LANGUAGE_NAMES = {'en': 'English', 'no': 'Norwegian'}
DEFAULT_TARGETS = {'en': 3, 'no': 2}
MIN_ORIGINAL_LINE_BREAKS = 50
# Bump for matching/search changes; unrelated updates must not reopen searches.
MATCHING_POLICY_REVISION = 4
RETRY_POLICY_REVISION = 1
AUTO_RETRY_DELAYS = (3600, 6 * 3600, 24 * 3600)
SCRIPT_VERSION = '2026.10.17.2'


def language_group(language):
    if language.alpha3 == 'eng':
        return 'en'
    if language.alpha3 in {'nor', 'nob', 'nno'}:
        return 'no'
    return None


def filename_language(video, filename):
    match = re.fullmatch(re.escape(video.stem) +
                         r'\.(en|no|nb|nn)\.[1-9][0-9]*(?:\.hi)?\.srt', filename)
    if match:
        return 'en' if match[1] == 'en' else 'no'
    # Old names are still present during a preview of their migration.
    match = re.fullmatch(re.escape(video.stem) +
                         r'\.subliminal-[A-Za-z0-9_-]+-[0-9a-f]{16}\.(en|no)(?:\.hi)?\.srt', filename)
    return match[1] if match else None


@dataclass
class VideoResult:
    saved: int
    candidates: int
    kept: int = 0
    skipped: bool = False
    quota_exhausted: bool = False
    rate_limited: bool = False
    errors: int = 0


class SyncDependencyError(RuntimeError):
    """Stop before spending download allowance when sync cannot run."""


class SyncError(RuntimeError):
    """Keep downloaded input for a later retry."""


class SyncRejected(SyncError):
    """An alignment was rejected rather than published as a usable subtitle."""


@contextmanager
def timeline_alignments():
    """Keep subtitle speech on the video timeline during the global search."""
    import importlib
    import numpy as np
    module = importlib.import_module('ffsubsync.ffsubsync')
    speech_module = importlib.import_module('ffsubsync.speech_transformers')
    original = module.FFTAligner
    original_progress = speech_module.tqdm

    def quiet_progress(*args, **kwargs):
        kwargs['disable'] = True
        return original_progress.tqdm(*args, **kwargs)

    class TimelineAligner(original):
        def fit(self, refstring, substring, get_score=False):
            values = list(map(int, substring)) if isinstance(substring, str) else substring
            speech = np.flatnonzero(np.asarray(values) > 0.5)
            if not len(speech):
                from ffsubsync.aligners import FailedToFindAlignmentException
                raise FailedToFindAlignmentException('Subtitles contain no speech to align')
            # At most 10% may fall off either end (at least 80% stays in view).
            # This bounds overlap, not the number of seconds an offset may have.
            clipped = int(len(speech) * 0.10)
            self.timeline_min = -int(speech[clipped])
            self.timeline_max = len(refstring) - 1 - int(speech[-clipped - 1])
            return super().fit(refstring, substring, get_score=get_score)

        def _eliminate_extreme_offsets_from_solutions(self, convolve, substring):
            scores = super()._eliminate_extreme_offsets_from_solutions(convolve, substring)
            # FFTAligner's output index decreases as the applied offset grows.
            origin = len(scores) - 1 - len(substring)
            first = max(0, origin - self.timeline_max)
            last = min(len(scores), origin - self.timeline_min + 1)
            if first >= last:
                scores[:] = float('-inf')
            else:
                scores[:first] = float('-inf')
                scores[last:] = float('-inf')
            return scores

    # ffsubsync 0.5.1 selects its aligner from this module. Limit the override
    # to this one synchronous call; the installed package is never modified.
    module.FFTAligner = TimelineAligner
    if not sys.stdout.isatty():
        speech_module.tqdm = SimpleNamespace(tqdm=quiet_progress)
    try:
        yield
    finally:
        module.FFTAligner = original
        speech_module.tqdm = original_progress


class SyncRejectionDiagnostics(logging.Handler):
    def __init__(self):
        super().__init__(level=logging.WARNING)
        self.reason = None

    def emit(self, record):
        message = record.getMessage()
        if 'low-quality alignment' in message:
            self.reason = message


class SubtitleSynchronizer:
    """Lazy, audio-based sync; reuse the speech signal within one video."""
    def __init__(self, video):
        self.video = Path(video).absolute()
        self.temporary = None
        self.runner = self.parser = None
        self.cache = self.reference = None

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        if self.temporary is not None:
            self.temporary.cleanup()

    def ensure_ready(self):
        if self.runner is not None:
            return
        missing = [name for name in ('ffmpeg', 'ffprobe') if shutil.which(name) is None]
        if missing:
            raise SyncDependencyError('Missing ' + ', '.join(missing) +
                                      '. Install them with: sudo apt install ffmpeg')
        try:
            from ffsubsync import run
            from ffsubsync.ffsubsync import make_parser
            parser = make_parser()
        except ImportError as error:
            raise SyncDependencyError("Install sync support with: pipx inject subliminal 'ffsubsync==0.5.1'") from error
        if '--skip-sync-on-low-quality' not in parser._option_string_actions:
            raise SyncDependencyError("Update sync support with: pipx inject subliminal 'ffsubsync==0.5.1'")
        try:
            probe = subprocess.run(
                ['ffprobe', '-v', 'error', '-show_entries', 'stream=codec_type',
                 '-of', 'json', str(self.video)],
                capture_output=True, text=True, timeout=20, check=False)
            streams = json.loads(probe.stdout).get('streams', []) if probe.returncode == 0 else []
        except (OSError, ValueError, subprocess.TimeoutExpired) as error:
            raise SyncError('Cannot inspect the video audio; no subtitle download attempted.') from error
        if not any(stream.get('codec_type') == 'audio' for stream in streams):
            raise SyncError('No readable audio track; no subtitle download attempted.')
        self.runner, self.parser = run, parser

    def sync(self, content):
        self.ensure_ready()
        if self.temporary is None:
            self.temporary = tempfile.TemporaryDirectory(prefix='getsubs-sync-')
            folder = Path(self.temporary.name)
            self.reference = folder / ('reference' + self.video.suffix)
            self.reference.symlink_to(self.video)
            self.cache = folder / 'reference.npz'
        folder = Path(self.temporary.name)
        source, target = folder / 'input.srt', folder / 'output.srt'
        source.write_bytes(content)
        target.unlink(missing_ok=True)
        reference = self.cache if self.cache.is_file() else self.reference
        options = [str(reference), '-i', str(source), '-o', str(target),
                   '--encoding', 'utf-8', '--output-encoding', 'utf-8',
                   '--skip-sync-on-low-quality', '--gui-mode']
        if reference == self.reference:
            options += ['--vad', 'webrtc', '--serialize-speech']
        args = self.parser.parse_args(options)
        # The Python aligner supports an unbounded global search with None.
        # Keep correlation checks, but never reject solely for a large shift.
        args.max_offset_seconds = None
        args.quality_max_offset_seconds = float('inf')
        last_progress = -1

        def progress(info):
            nonlocal last_progress
            if info.fraction is not None:
                step = int(info.fraction * 4)
                if step > last_progress:
                    last_progress = step
                    print(f'  Analyzing audio: {min(100, step * 25)}%', flush=True)

        diagnostics = SyncRejectionDiagnostics()
        sync_logger = logging.getLogger('ffsubsync')
        sync_logger.addHandler(diagnostics)
        try:
            with timeline_alignments():
                result = self.runner(args, progress_handler=progress)
        except Exception as error:
            raise SyncError(f'Could not synchronize: {error}') from error
        finally:
            sync_logger.removeHandler(diagnostics)
        if not result.get('sync_was_successful'):
            if target.is_file() and target.stat().st_size:
                reason = diagnostics.reason or 'alignment reported unsuccessful'
                raise SyncRejected(f'ffsubsync rejected the alignment: {reason}. '
                                   'No subtitle was published.')
            raise SyncError('ffsubsync could not produce a synchronized subtitle.')
        if result.get('retval') or not target.is_file():
            raise SyncError('ffsubsync failed to write its output.')
        output = target.read_bytes()
        try:
            import srt
            cues = list(srt.parse(output.decode('utf-8-sig')))
            if not cues or not any(cue.end > cue.start for cue in cues):
                raise ValueError('No usable subtitle cues')
        except (ValueError, UnicodeError, srt.SRTParseError) as error:
            raise SyncError('ffsubsync produced an invalid SRT file.') from error
        if self.cache.is_file():
            import numpy as np
            from ffsubsync.constants import SAMPLE_RATE
            with np.load(self.cache, allow_pickle=False) as saved:
                duration = len(saved['speech']) / SAMPLE_RATE
            total = visible = 0.0
            for cue in cues:
                start, end = cue.start.total_seconds(), cue.end.total_seconds()
                total += max(0.0, end - start)
                visible += max(0.0, min(duration, end) - max(0.0, start))
            if not total or visible / total < 0.80:
                raise SyncRejected('Aligned subtitles mostly fall outside the video timeline; '
                                   'no subtitle was published.')
        offset, speed = result.get('offset_seconds'), result.get('framerate_scale_factor')
        if offset is not None and speed is not None:
            print(f'  Synced: offset {offset:+.2f}s; speed factor {speed:.5f}.', flush=True)
        return output


class QuotaAwarePool(ProviderPool):
    """Observe OpenSubtitles quota before Subliminal consumes its exceptions."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.quota_exhausted = False
        self.quota_reset = None
        self.rate_limited = False
        self.video_failed_providers = set()
        self._watched = set()

    def begin_video(self):
        self.video_failed_providers.clear()

    def list_subtitles_provider(self, provider, video, languages):
        result = super().list_subtitles_provider(provider, video, languages)
        if result.failure() or result.outage():
            self.video_failed_providers.add(provider)
        return result

    def list_subtitles(self, video, languages):
        # Failed providers remain in Subliminal's run-wide error summary, but
        # a recovered error on an earlier film must not poison later markers.
        for name in self.discarded_providers:
            plugin = provider_manager[name].plugin
            if plugin.check(video) and plugin.check_languages(languages):
                self.video_failed_providers.add(name)
        return super().list_subtitles(video, languages)

    def _request(self, request, *args, **kwargs):
        for attempt in range(4):
            try:
                return request(*args, **kwargs)
            except ProviderRateLimited as error:
                if attempt == 3 or error.wait > 30:
                    self.rate_limited = True
                    print('OpenSubtitles is temporarily rate-limited; pausing this scan. '
                          'Progress is kept for the next run.', flush=True)
                    raise
                print(f'OpenSubtitles rate limit: waiting {error.wait:g}s '
                      f'before retry {attempt + 1}/3.', flush=True)
                time.sleep(error.wait)

    def _rate_limit_response(self, response, **kwargs):
        if response.status_code == 429:
            raw = response.headers.get('Retry-After', '')
            try:
                delay = float(raw)
            except (ValueError, TypeError):
                try:
                    until = parsedate_to_datetime(raw)
                    if until.tzinfo is None:
                        until = until.replace(tzinfo=timezone.utc)
                    delay = (until - datetime.now(timezone.utc)).total_seconds()
                except (ValueError, TypeError, OverflowError):
                    delay = 3.0
            if hasattr(response, 'close'):
                response.close()
            raise ProviderRateLimited(max(1.0, delay))
        return response

    def _record_quota(self, data):
        if not isinstance(data, dict):
            return None
        try:
            remaining = int(data['remaining'])
        except (KeyError, TypeError, ValueError):
            return None
        if remaining <= 0:
            self.quota_exhausted = True
            self.quota_reset = data.get('reset_time_utc') or data.get('reset_time')
        return remaining

    def _download_response(self, response, **kwargs):
        if not urlsplit(response.url).path.rstrip('/').endswith('/download'):
            return response
        try:
            data = response.json()
        except ValueError:
            data = {}
        remaining = self._record_quota(data)
        if response.status_code == 407:
            self.quota_exhausted = True
        if self.quota_exhausted:
            # remaining=0 with a successful link is the LAST allowed download.
            # Let it finish, then stop before any further provider request.
            if response.status_code == 200 and remaining == 0 and data.get('link'):
                return response
            raise DownloadLimitReached('OpenSubtitles download allowance exhausted')
        return response

    def __getitem__(self, name):
        provider = super().__getitem__(name)
        if not name.startswith('opensubtitlescom') or id(provider) in self._watched:
            return provider
        self._watched.add(id(provider))
        provider.session.hooks.setdefault('response', []).append(self._rate_limit_response)
        provider.session.hooks.setdefault('response', []).append(self._download_response)
        original_request = provider.session.request

        @wraps(original_request)
        def request(*args, **kwargs):
            return self._request(original_request, *args, **kwargs)

        # Cover API searches, login, and the actual subtitle file transfer.
        provider.session.request = request
        original = provider.api_post

        @wraps(original)
        def api_post(path, *args, **kwargs):
            try:
                data = original(path, *args, **kwargs)
            except DownloadLimitExceeded:
                self.quota_exhausted = True
                raise
            if path.rstrip('/') == 'download':
                remaining = self._record_quota(data)
                if remaining == 0 and data.get('link'):
                    # Subliminal 2.8 rejects a usable last link when remaining
                    # reaches zero. Preserve that link without another API call.
                    return {**data, 'remaining': 1}
            return data

        provider.api_post = api_post
        original_get = provider.api_get

        @wraps(original_get)
        def api_get(path, params=None, **kwargs):
            params = dict(params) if params else {}
            selectors = {'query', 'imdb_id', 'tmdb_id', 'parent_imdb_id',
                         'parent_tmdb_id', 'id'}
            if (path.rstrip('/') == 'subtitles' and params.get('moviehash')
                    and not any(params.get(key) for key in selectors)):
                # With the default "include", an unknown hash alone can fall
                # back to a catalogue-wide search. Other criteria still search
                # by title/ID, so restricting this one does not lose fallback.
                params['moviehash_match'] = 'only'
            return original_get(path, params, **kwargs)

        provider.api_get = api_get
        original_criteria = provider._make_query

        @wraps(original_criteria)
        def movie_criteria(**kwargs):
            criteria = original_criteria(**kwargs)
            if kwargs.get('year') is not None:
                for criterion in criteria:
                    if criterion.get('query'):
                        criterion['year'] = kwargs['year']
            unique = []
            for criterion in criteria:
                if criterion not in unique:
                    unique.append(criterion)
            return unique

        provider._make_query = movie_criteria
        original_list = provider.list_subtitles

        @wraps(original_list)
        def list_subtitles(video, languages):
            if not isinstance(video, Movie):
                return original_list(video, languages)
            options = {'allow_machine_translated': False, 'sort_by_download_count': True}
            moviehash = video.hashes.get(provider.subtitle_class.provider_name)
            if moviehash:
                found = provider.query(languages, moviehash=moviehash, **options)
                if found:
                    return found
            # Upstream 2.8.0 omits the movie year and TMDB ID here. Preserve
            # the year even in its secondary title-only search criteria.
            return provider.query(
                languages, query=video.title, year=video.year,
                imdb_id=video.external_ids.get('imdb_id'),
                tmdb_id=video.external_ids.get('tmdb_id'), **options)

        provider.list_subtitles = list_subtitles
        return provider


class ProviderRateLimited(RuntimeError):
    def __init__(self, wait):
        self.wait = wait
        super().__init__('OpenSubtitles temporarily rate-limited this request')


def provider_paused(pool):
    return (getattr(pool, 'quota_exhausted', False)
            or getattr(pool, 'rate_limited', False))


def auxiliary_video(path):
    name = path.name.casefold()
    return (name.startswith('~utorrentpartfile_')
            or path.stem.casefold() in {'rarbg.com', 'www.rarbg.com', 'sample'}
            or re.search(r'[._-]sample$', path.stem.strip(), re.I))


class OptionalMkvmergeWarning(logging.Filter):
    """Do not warn about an optional backend when MediaInfo is available."""
    def filter(self, record):
        if 'mkvmerge not found' not in record.getMessage():
            return True
        from knowit.api import available_providers
        mediainfo = available_providers.get('mediainfo')
        return not (mediainfo is not None and mediainfo.loaded())


def video_paths(paths):
    """Walk folders without following directory symlinks; deduplicate inputs."""
    seen = set()
    for raw in paths:
        path = Path(raw).expanduser().absolute()
        if not path.exists():
            raise ValueError(f'Path does not exist: {path}')
        if path.is_dir():
            def walk_error(error):
                raise error
            def walk_files():
                for root, dirs, names in os.walk(path, onerror=walk_error):
                    dirs[:] = [name for name in dirs if name.casefold() not in {'sample', 'samples'}]
                    dirs.sort()
                    for name in sorted(names):
                        file = Path(root) / name
                        if file.suffix.lower() in MEDIA_EXTENSIONS and auxiliary_video(file):
                            print(f'Skipping sample, ad, or torrent support file: {file}', flush=True)
                            continue
                        yield file
            files = walk_files()
        else:
            if path.suffix.lower() not in MEDIA_EXTENSIONS:
                raise ValueError(f'Unsupported video extension: {path}')
            files = [path]
        for file in files:
            if file.suffix.lower() not in MEDIA_EXTENSIONS or not file.is_file():
                continue
            identity = os.path.realpath(file)
            if identity not in seen:
                seen.add(identity)
                yield file


def prioritized_video_paths(paths):
    """Give unattempted videos their first chance before revisiting gaps."""
    previous = []
    for path in video_paths(paths):
        marker = path.with_name(f'.{path.name}.sublime_finished.json')
        if os.path.lexists(marker):
            previous.append(path)
        else:
            yield path
    yield from previous


def scan_media_video(path):
    # A collection folder can replace a complete filename's title and year.
    # Prefer dated movie filenames; retain path context for short episode names
    # and movies whose year is only supplied by their own folder.
    known_extension = path.suffix.lower() in VIDEO_EXTENSIONS
    filename = path.name if known_extension else path.with_suffix('.mkv').name
    try:
        named = scan_name(str(path), name=filename)
    except ValueError:
        named = None
    if isinstance(named, Movie) and named.title and named.year is not None:
        named.size = path.stat().st_size
        return named
    if known_extension:
        return scan_video(str(path))
    # The normal scanner rejects extensions outside its own fixed list. Use
    # the same filename parser with a recognized suffix while retaining the
    # actual video path for hashing, metadata, and all filesystem operations.
    video = scan_name(str(path), name=str(path.with_suffix('.mkv')))
    video.size = path.stat().st_size
    return video


def subtitle_identity(subtitle):
    provider = re.sub(r'[^a-zA-Z0-9_-]', '_', subtitle.provider_name)
    identity = f'{subtitle.provider_name}\n{subtitle.id}'.encode('utf-8')
    token = hashlib.sha256(identity).hexdigest()[:16]
    return provider, token


class VideoMarker:
    """Keep completion and retry progress beside this particular video."""
    def __init__(self, video, dry_run=False, targets=None):
        self.video = Path(video)
        self.targets = dict(DEFAULT_TARGETS if targets is None else targets)
        self.filename = self.video.with_name(f'.{self.video.name}.sublime_finished.json')
        self.dry_run = dry_run
        self.signature = self.video_signature()
        self.adopt_existing = not os.path.lexists(self.filename)
        self.policy_rechecks = []
        self.retry_rejected_keys = set()
        self.adopted_changed = False
        self.retry_migrated = False
        self.ready_languages = set()
        self.attempted_languages = {}
        self.data = {
            'version': 4, 'video': self.video.name, 'signature': self.signature,
            'matching_revision': MATCHING_POLICY_REVISION,
            'finished': False, 'done': {}, 'subtitles': {}, 'adopted': [],
            'pending': {}, 'rejected': {},
            'rejection_revisions': {},
            'movie_identity': {},
            'retry_manually': False,
            'retry_policy_revision': RETRY_POLICY_REVISION,
            'retry_schedule': {},
            'requested_counts': self.targets,
            'import_legacy': True,
        }
        if not self.adopt_existing:
            if self.filename.is_symlink() or not self.filename.is_file():
                raise ValueError(f'Completion marker is not a regular file: {self.filename}')
            try:
                data = json.loads(self.filename.read_text(encoding='utf-8'))
                valid = (
                    isinstance(data, dict) and data.get('version') in (1, 2, 3, 4)
                    and isinstance(data.get('signature'), dict)
                    and isinstance(data.get('finished'), bool)
                    and isinstance(data.get('subtitles'), dict)
                    and isinstance(data.get('adopted'), list)
                )
                if not valid:
                    raise ValueError('Unrecognized marker format')
                old_policy = data['version'] < 4
                matching_revision = data.get('matching_revision', 0)
                if (type(matching_revision) is not int
                        or not 0 <= matching_revision <= MATCHING_POLICY_REVISION):
                    raise ValueError('Invalid or unsupported matching-policy revision')
                if data['version'] == 1:
                    count = data.get('requested_count')
                    if not isinstance(count, int) or count < 0:
                        raise ValueError('Invalid requested count')
                    data['done'] = {'en': count} if data['finished'] else {}
                    data.pop('requested_count', None)
                data['version'] = 4
                data['matching_revision'] = MATCHING_POLICY_REVISION
                data.setdefault('pending', {})
                data.setdefault('rejected', {})
                data.setdefault('rejection_revisions', {})
                data.setdefault('movie_identity', {})
                data.setdefault('retry_manually', False)
                retry_revision = data.get('retry_policy_revision', 0)
                if (type(retry_revision) is not int
                        or not 0 <= retry_revision <= RETRY_POLICY_REVISION):
                    raise ValueError('Invalid or unsupported automatic retry policy')
                data.setdefault('retry_schedule', {})
                if not isinstance(data['retry_schedule'], dict):
                    raise ValueError('Invalid automatic retry schedule')
                for code, entry in data['retry_schedule'].items():
                    if (code not in LANGUAGES or not isinstance(entry, dict)
                            or type(entry.get('failures', 0)) is not int
                            or entry.get('failures', 0) < 0
                            or type(entry.get('last_count', 0)) is not int
                            or entry.get('last_count', 0) < 0
                            or type(entry.get('target', self.targets[code])) is not int
                            or entry.get('target', self.targets[code]) < 1
                            or type(entry.get('retry_rejected', False)) is not bool
                            or any(type(entry.get(key, 0)) not in (int, float)
                                   or not 0 <= entry.get(key, 0) <= 253402300799
                                   for key in ('checked_at', 'next_at'))):
                        raise ValueError('Invalid automatic retry entry')
                if not isinstance(data['retry_manually'], bool):
                    raise ValueError('Invalid retry policy')
                identity = data['movie_identity']
                if (not isinstance(identity, dict)
                        or any(not isinstance(identity.get(name, ''), str)
                               for name in ('title', 'imdb_id', 'tmdb_id'))
                        or (identity.get('year') is not None and not isinstance(identity['year'], int))):
                    raise ValueError('Invalid cached movie identity')
                if (not isinstance(data.get('done'), dict)
                        or not all(code in LANGUAGES and isinstance(count, int) and count >= 0
                                   for code, count in data['done'].items())):
                    raise ValueError('Invalid completed languages')
                names = [*data['subtitles'].values(), *data['adopted']]
                if not all(isinstance(name, str) and name not in ('', '.', '..')
                           and Path(name).name == name for name in names):
                    raise ValueError('Invalid subtitle filename')
                if not isinstance(data['pending'], dict) or not isinstance(data['rejected'], dict):
                    raise ValueError('Invalid sync progress')
                if not all(isinstance(key, str) and isinstance(reason, str)
                           for key, reason in data['rejected'].items()):
                    raise ValueError('Invalid rejected subtitles')
                if (not isinstance(data['rejection_revisions'], dict)
                        or not all(isinstance(key, str) and type(revision) is int
                                   and 0 <= revision <= MATCHING_POLICY_REVISION
                                   for key, revision in data['rejection_revisions'].items())):
                    raise ValueError('Invalid rejection policy revisions')
                for key, entry in data['pending'].items():
                    if (not isinstance(key, str) or not isinstance(entry, dict)
                            or entry.get('language') not in LANGUAGES
                            or entry.get('mode') not in ('hash', 'sync')
                            or not isinstance(entry.get('content'), str)
                            or not isinstance(entry.get('hearing_impaired'), bool)):
                        raise ValueError('Invalid cached subtitle')
                    if 'output' in entry and not isinstance(entry['output'], str):
                        raise ValueError('Invalid cached output')
                    if 'target' in entry and (not isinstance(entry['target'], str)
                            or filename_language(self.video, entry['target']) != entry['language']):
                        raise ValueError('Invalid cached subtitle target')
            except (ValueError, UnicodeError) as error:
                raise ValueError(f'Cannot read completion marker {self.filename}; '
                                 'remove it to retry.') from error
            if data.get('video') == self.video.name and data['signature'] == self.signature:
                self.data = data
                self.retry_migrated = retry_revision < RETRY_POLICY_REVISION
                self.data['retry_policy_revision'] = RETRY_POLICY_REVISION
                if matching_revision < MATCHING_POLICY_REVISION or self.retry_migrated:
                    self.adopt_numbered()
                if old_policy:
                    # Older empty/short searches excluded lower-scoring subs.
                    # Revisit those once, retaining every file already saved.
                    for code, count in list(data['done'].items()):
                        if len(self.files(code)) < count:
                            data['done'].pop(code)
                if matching_revision < MATCHING_POLICY_REVISION or self.retry_migrated:
                    for code, target in self.targets.items():
                        if len(self.files(code)) < target:
                            data['done'].pop(code, None)
                            data['finished'] = False
                            data['retry_manually'] = False
                            data['retry_schedule'][code] = {'retry_rejected': True}
                            self.policy_rechecks.append(code)
            else:
                # Keep old subtitles, but do not count them as matches for a
                # replacement video. New alternatives get the next free number.
                print('Video has changed; searching again and preserving old subtitles.', flush=True)
                self.data['import_legacy'] = False
        else:
            self.adopt_numbered()

    def video_signature(self):
        stat = self.video.stat()
        return {'size': stat.st_size, 'mtime_ns': stat.st_mtime_ns}

    def files(self, language=None):
        names = dict.fromkeys([*self.data['subtitles'].values(), *self.data['adopted']])
        return [self.video.with_name(name) for name in names
                if (language is None or filename_language(self.video, name) == language)
                if self.video.with_name(name).is_file()
                and not self.video.with_name(name).is_symlink()]

    def language_finished(self, language, count):
        return len(self.files(language)) >= count

    def finished(self, count=None):
        targets = self.targets if count is None else {**self.targets, 'en': count}
        return all(self.language_finished(code, target) for code, target in targets.items())

    def counts(self):
        return '; '.join(f'{LANGUAGE_NAMES[code]} {len(self.files(code))}/{target}'
                         for code, target in self.targets.items())

    def retry_at(self, code):
        entry = self.data['retry_schedule'].get(code, {})
        # Added or deleted files change the work required; check it now.
        if 'last_count' in entry and entry['last_count'] != len(self.files(code)):
            return 0
        if entry.get('target', self.targets[code]) != self.targets[code]:
            return 0
        return entry.get('next_at', 0)

    def prepare_retries(self, *, force=False):
        now = time.time()
        self.ready_languages.clear()
        for code, target in self.targets.items():
            if self.language_finished(code, target):
                continue
            if force or self.retry_at(code) <= now:
                self.ready_languages.add(code)
                state = self.data['retry_schedule'].get(code, {})
                if force or state.get('retry_rejected', False):
                    self.retry_rejected_keys.update(
                        key for key in self.data['rejected'] if key.split(':', 1)[0] == code)
        return self.ready_languages

    def start_attempt(self, code):
        self.attempted_languages.setdefault(code, len(self.files(code)))

    def next_retry_text(self, code=None):
        times = [self.retry_at(lang) for lang, target in self.targets.items()
                 if (code is None or code == lang)
                 and not self.language_finished(lang, target)]
        when = min(times) if times else 0
        if when <= time.time():
            return 'the next folder scan'
        return datetime.fromtimestamp(when, timezone.utc).strftime('%Y-%m-%d %H:%M UTC')

    def adopt_numbered(self):
        if self.data.get('import_legacy', True):
            pattern = re.compile(re.escape(self.video.stem) + r'\.(?:en|no|nb|nn)\.[1-9][0-9]*(?:\.hi)?\.srt')
            owned = set(self.data['subtitles'].values())
            names = set(self.data['adopted']) | {
                file.name for file in self.video.parent.iterdir()
                if pattern.fullmatch(file.name) and file.is_file()
                and not file.is_symlink() and file.name not in owned}
            adopted = sorted(names)
            self.adopted_changed |= adopted != self.data['adopted']
            self.data['adopted'] = adopted

    def rejection_blocks(self, key):
        return (key in self.data['rejected'] and key not in self.retry_rejected_keys
                and self.data['rejection_revisions'].get(key, 0) >= MATCHING_POLICY_REVISION)

    def lookup(self, provider, token, language=None):
        codes = (language,) if language else LANGUAGES
        for code in codes:
            name = (self.data['subtitles'].get(f'{code}:{provider}:{token}')
                    or self.data['subtitles'].get(f'{provider}:{token}'))
            if name is not None and filename_language(self.video, name) == code:
                return self.video.with_name(name)
        return None

    def remember(self, provider, token, target, *, persist=True):
        code = filename_language(self.video, target.name)
        self.data['subtitles'][f'{code}:{provider}:{token}'] = target.name
        self.data['done'].pop(code, None)
        if persist:
            self.save()

    def stage(self, subtitle, code, mode, content):
        provider, token = subtitle_identity(subtitle)
        key = f'{code}:{provider}:{token}'
        self.data['pending'][key] = {
            'language': code, 'mode': mode, 'content': content.decode('utf-8-sig'),
            'hearing_impaired': bool(subtitle.hearing_impaired),
            'label': f'{subtitle.provider_name} {subtitle.id}',
        }
        self.data['done'].pop(code, None)
        self.save()
        return key

    def finish_pending(self, key, target):
        entry = self.data['pending'].pop(key)
        self.data['subtitles'][key] = target.name
        self.data['rejected'].pop(key, None)
        self.data['rejection_revisions'].pop(key, None)
        self.retry_rejected_keys.discard(key)
        self.data['done'].pop(entry['language'], None)
        self.save()

    def reject_pending(self, key, reason):
        # Retain raw input, but treat this rejected entry as inactive until a
        # new policy or an explicit filename authorizes another attempt.
        self.data['rejected'][key] = str(reason)
        self.data['rejection_revisions'][key] = MATCHING_POLICY_REVISION
        self.retry_rejected_keys.discard(key)
        self.save()

    def record_attempt(self, *, quota_exhausted=False):
        """Schedule missing languages automatically; pauses resume immediately."""
        if self.dry_run:
            return
        self.data['retry_manually'] = False
        now = time.time()
        for code, before in self.attempted_languages.items():
            count = len(self.files(code))
            if count >= self.targets[code]:
                self.data['retry_schedule'].pop(code, None)
                continue
            state = self.data['retry_schedule'].get(code, {})
            if quota_exhausted:
                # Keep any policy recheck permission until an attempt completes.
                state['next_at'] = 0
                self.data['retry_schedule'][code] = state
                continue
            failures = 1 if count > before else state.get('failures', 0) + 1
            delay = AUTO_RETRY_DELAYS[min(failures - 1, len(AUTO_RETRY_DELAYS) - 1)]
            self.data['retry_schedule'][code] = {
                'checked_at': now, 'next_at': now + delay,
                'failures': failures, 'last_count': count,
                'target': self.targets[code],
                'retry_rejected': False,
            }
        self.save()

    def save(self):
        if self.dry_run:
            return
        if self.video_signature() != self.signature:
            raise ValueError('Video changed during processing; it has not been marked finished.')
        # A deleted alternative invalidates only its own language's completion.
        present = {file.name for file in self.files()}
        expected = set(self.data['subtitles'].values()) | set(self.data['adopted'])
        for name in expected - present:
            self.data['done'].pop(filename_language(self.video, name), None)
        self.data['subtitles'] = {key: name for key, name in self.data['subtitles'].items()
                                 if name in present}
        self.data['adopted'] = [name for name in self.data['adopted'] if name in present]
        self.data['requested_counts'] = self.targets
        self.data['retry_manually'] = False
        self.data['finished'] = self.finished()
        # "done" now means files actually exist, never just "search exhausted".
        self.data['done'] = {code: target for code, target in self.targets.items()
                             if self.language_finished(code, target)}
        for code in self.data['done']:
            self.data['retry_schedule'].pop(code, None)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8',
                                             dir=self.video.parent, prefix='.sublime-',
                                             suffix='.tmp', delete=False) as stream:
                temporary = Path(stream.name)
                json.dump(self.data, stream, ensure_ascii=False, indent=2)
                stream.write('\n')
                stream.flush()
                os.fsync(stream.fileno())
            os.replace(temporary, self.filename)
            self.adopted_changed = False
        finally:
            if temporary is not None:
                temporary.unlink(missing_ok=True)


def output_path(video_path, number, hearing_impaired=False, language='en'):
    category = '.hi' if hearing_impaired else ''
    return video_path.with_name(f'{video_path.stem}.{language}.{number}{category}.srt')


def next_output_path(video_path, hearing_impaired=False, reserved=None, language='en'):
    reserved = reserved if reserved is not None else set()
    number = 1
    while True:
        codes = ('no', 'nb', 'nn') if language == 'no' else ('en',)
        alternatives = [output_path(video_path, number, hi, code)
                        for code in codes for hi in (False, True)]
        if not any(os.path.lexists(p) or p in reserved for p in alternatives):
            return output_path(video_path, number, hearing_impaired, language)
        number += 1


def migrate_legacy_names(path, marker, *, dry_run=False, reserved=None):
    """Rename only files made by older wrapper versions; never replace a file."""
    if not marker.data.get('import_legacy', True):
        return 0
    reserved = reserved if reserved is not None else set()
    pattern = re.compile(re.escape(path.stem) +
                         r'\.subliminal-(?P<provider>[A-Za-z0-9_-]+)-'
                         r'(?P<token>[0-9a-f]{16})\.(?P<language>en|no)(?P<hi>\.hi)?\.srt')
    changed = 0
    for old in sorted(path.parent.iterdir()):
        match = pattern.fullmatch(old.name)
        if not match or old.is_symlink() or not old.is_file():
            continue
        provider, token = match.group('provider', 'token')
        target = next_output_path(path, bool(match['hi']), reserved, match['language'])
        if dry_run:
            reserved.add(target)
            marker.remember(provider, token, old, persist=False)
            print(f'Would rename {old.name} -> {target.name}', flush=True)
        else:
            # Same-directory hard-link + unlink preserves bytes and metadata, and
            # unlike plain os.rename cannot replace a racing destination file.
            while True:
                try:
                    os.link(old, target)
                    break
                except FileExistsError:
                    target = next_output_path(path, bool(match['hi']), reserved, match['language'])
            # Persist the ID before removing the old name. If this fails, the
            # original file still exists and no subtitle content is lost.
            marker.remember(provider, token, target)
            old.unlink()
            print(f'Renamed {old.name} -> {target.name}', flush=True)
        changed += 1
    return changed


def write_new(path, content):
    """Exclusive creation also protects files/symlinks created during a run."""
    try:
        with path.open('xb') as stream:
            stream.write(content)
    except FileExistsError:
        return False
    return True


def subtitle_line_breaks(content):
    """Count LF, CRLF, and CR once each, including BOM-encoded SRT files."""
    if content.startswith((b'\xff\xfe\x00\x00', b'\x00\x00\xfe\xff')):
        encoding = 'utf-32'
    elif content.startswith((b'\xff\xfe', b'\xfe\xff')):
        encoding = 'utf-16'
    else:
        # Replacement characters preserve line breaks in legacy byte encodings.
        encoding = 'utf-8-sig'
    text = content.decode(encoding, errors='replace')
    return text.count('\n') + text.count('\r') - text.count('\r\n')


def copy_original_subtitle(path, *, dry_run=False):
    """Give an exact-name original its own preferred English slot; never replace."""
    source = path.with_suffix('.srt')
    if source.is_symlink() or not source.is_file():
        return 0
    target = path.with_name(f'{path.stem}.en.0.default.srt')
    content = source.read_bytes()
    breaks = subtitle_line_breaks(content)
    if breaks < MIN_ORIGINAL_LINE_BREAKS:
        print(f'Skipping preferred original copy: {source.name} has {breaks} '
              f'line breaks (minimum {MIN_ORIGINAL_LINE_BREAKS}).', flush=True)
        return 0

    def existing_destination():
        if target.is_file() and not target.is_symlink() and target.read_bytes() == content:
            return
        print(f'Original copy not made: {target.name} already exists; '
              'keeping it unchanged.', flush=True)

    if os.path.lexists(target):
        existing_destination()
        return 0
    if dry_run:
        print(f'Would copy original {source.name} -> {target.name} '
              '(assumed English; preferred track).', flush=True)
        return 0
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=path.parent, prefix='.sublime-original-',
                                         suffix='.tmp', delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(content)
            stream.flush()
            os.fsync(stream.fileno())
        shutil.copymode(source, temporary)
        try:
            # Publish a complete, independent copy exclusively. The temporary
            # link is removed below; it never shares an inode with the original.
            os.link(temporary, target)
        except FileExistsError:
            existing_destination()
            return 0
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    print(f'Copied original {source.name} -> {target.name} '
          '(assumed English; preferred track).', flush=True)
    return 1


def ranked_candidates(video, subtitles, minimum, categories, skip_wrong_fps, language='en'):
    maximum = get_scores(video)['hash']
    threshold = maximum * minimum // 100
    subtitles = filter_and_sort_categories(subtitles, subtitle_categories=categories)
    ranked = []
    seen = set()
    for subtitle in subtitles:
        if language_group(subtitle.language) != language:
            continue
        identity = (subtitle.provider_name, str(subtitle.id), subtitle.language)
        if identity in seen:
            continue
        seen.add(identity)
        if skip_wrong_fps and video.frame_rate and not fps_matches(
            video, fps=subtitle.fps, strict=False
        ):
            continue
        score = compute_score(subtitle, video)
        if score >= threshold:
            ranked.append((score, subtitle))
    # Stable ties retain provider/category ordering from the configuration.
    return sorted(ranked, key=lambda item: item[0], reverse=True)


def movie_title_tokens(title):
    if not isinstance(title, str):
        return []
    title = unicodedata.normalize('NFKD', title).casefold()
    title = ''.join(char for char in title if not unicodedata.combining(char))
    title = title.replace('&', ' and ').replace("'", '').replace('’', '')
    tokens = re.findall(r'[^\W_]+', title)
    romans = ('ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x', 'xi',
              'xii', 'xiii', 'xiv', 'xv', 'xvi', 'xvii', 'xviii', 'xix', 'xx')
    numbers = {roman: str(number) for number, roman in enumerate(romans, 2)}
    return [numbers.get(token, token) for token in tokens]


def movie_title_variants(title):
    """Only remove a separate sequel number surrounded by a substantial title."""
    tokens = movie_title_tokens(title)
    if len(tokens) < 6:
        return []
    variants = []
    for index, token in enumerate(tokens):
        if (index >= 2 and len(tokens) - index - 1 >= 2
                and token.isdigit() and 2 <= int(token) <= 20):
            variants.append(' '.join(tokens[:index] + tokens[index + 1:]))
    return list(dict.fromkeys(variants))[:2]


def movie_titles_match(video_title, subtitle_title):
    expected = movie_title_tokens(video_title)
    actual = movie_title_tokens(subtitle_title)
    return bool(expected and actual) and (expected == actual or
           ' '.join(actual) in movie_title_variants(video_title))


def same_video(video, subtitle):
    """Require content identity while allowing different releases and encodes."""
    matches = subtitle.get_matches(video)
    exact_id = bool({'imdb_id', 'tmdb_id', 'tvdb_id'} & matches)
    if isinstance(video, Episode):
        series = 'series' in matches or bool(
            {'series_imdb_id', 'series_tmdb_id', 'series_tvdb_id'} & matches)
        return exact_id or (series and {'season', 'episode'} <= matches)
    if isinstance(video, Movie):
        kind = getattr(subtitle, 'movie_kind', None)
        if kind is not None and str(kind).casefold() not in ('movie', 'film'):
            return False
        # Do not accidentally select a remake with the same title.
        years = [getattr(subtitle, attr, None) for attr in ('year', 'movie_year')]
        if video.year is not None and any(year is not None and year != video.year for year in years):
            return False
        for key, attr in (('imdb_id', 'movie_imdb_id'), ('tmdb_id', 'movie_tmdb_id')):
            known, found = video.external_ids.get(key), getattr(subtitle, attr, None)
            if known and found and str(known).lstrip('t0') != str(found).lstrip('t0'):
                return False
        if exact_id or ('title' in matches and (video.year is None or 'year' in matches)):
            return True
        title = getattr(subtitle, 'movie_title', None) or getattr(subtitle, 'title', None)
        return (video.year is not None and video.year in years
                and movie_titles_match(video.title, title))
    return False


def select_candidates(video, subtitles, categories, language):
    ranked = ranked_candidates(video, subtitles, 0, categories, False, language)
    hashes = [(score, subtitle) for score, subtitle in ranked
              if 'hash' in subtitle.get_matches(video)]
    if hashes:
        return hashes, 'hash'
    return [(score, subtitle) for score, subtitle in ranked if same_video(video, subtitle)], 'sync'


def apply_movie_identity(video, identity):
    """Use metadata identified by the file hash, keeping the file path intact."""
    if not isinstance(video, Movie) or not identity.get('title'):
        return False
    changed = video.title != identity['title']
    video.title = identity['title']
    if identity.get('year') is not None:
        changed |= video.year != identity['year']
        video.year = identity['year']
    for name in ('imdb_id', 'tmdb_id'):
        if identity.get(name):
            changed |= video.external_ids.get(name) != identity[name]
            video.external_ids[name] = identity[name]
    return changed


def learn_movie_identity(video, subtitles, marker, *, allow_title=False):
    """Cache identity from a hash or a conservative full-title/year match."""
    if not isinstance(video, Movie):
        return False
    selected = [subtitle for subtitle in subtitles if 'hash' in subtitle.get_matches(video)]
    source = 'File hash'
    if not selected and allow_title and not marker.data['movie_identity']:
        selected = [subtitle for subtitle in subtitles if same_video(video, subtitle)
                    and video.year is not None
                    and video.year in (getattr(subtitle, 'year', None),
                                       getattr(subtitle, 'movie_year', None))
                    and movie_titles_match(video.title, getattr(subtitle, 'movie_title', None)
                                           or getattr(subtitle, 'title', None))]
        source = 'Title and year'
    identities = []
    for subtitle in selected:
        title = getattr(subtitle, 'movie_title', None) or getattr(subtitle, 'title', None)
        if not isinstance(title, str) or not title.strip():
            continue
        year = getattr(subtitle, 'movie_year', None) or getattr(subtitle, 'year', None)
        if not isinstance(year, int):
            year = None
        imdb_id = str(getattr(subtitle, 'movie_imdb_id', None) or '')
        tmdb_id = str(getattr(subtitle, 'movie_tmdb_id', None) or '')
        identities.append((title.strip(), year, imdb_id, tmdb_id))
    if not identities:
        return False
    title, year, imdb_id, tmdb_id = Counter(identities).most_common(1)[0][0]
    identity = {'title': title, 'year': year, 'imdb_id': imdb_id, 'tmdb_id': tmdb_id}
    changed = apply_movie_identity(video, identity)
    marker.data['movie_identity'] = identity
    marker.save()
    if changed:
        label = f'{title} ({year})' if year is not None else title
        print(f'{source} identified the movie as: {label}', flush=True)
    return changed


def search_movie_title_variants(video, pool, marker, returned, categories, language):
    """Search a few plausible names, but validate every result against the original."""
    if not isinstance(video, Movie) or video.year is None:
        return returned, [], 'sync'
    combined = list(returned)
    seen = {(subtitle.provider_name, subtitle.id, subtitle.language) for subtitle in combined}
    for title in movie_title_variants(video.title):
        if provider_paused(pool):
            break
        print(f'Trying alternate movie title: {title} ({video.year})', flush=True)
        alias = copy.copy(video)
        alias.title = title
        alias.hashes = {}  # This is a title search; do not repeat hash queries.
        for subtitle in pool.list_subtitles(alias, LANGUAGES[language]):
            key = subtitle.provider_name, subtitle.id, subtitle.language
            if key not in seen:
                seen.add(key)
                combined.append(subtitle)
        candidates, mode = select_candidates(video, combined, categories, language)
        if candidates:
            if learn_movie_identity(video, [subtitle for _, subtitle in candidates],
                                    marker, allow_title=True):
                candidates, mode = select_candidates(video, combined, categories, language)
            return combined, candidates, mode
    return combined, [], 'sync'


def publish_pending(marker, key, synchronizer, fingerprints):
    """Sync and publish cached input; journal output before exclusive creation."""
    entry = marker.data['pending'][key]
    code = entry['language']
    if 'output' not in entry:
        content = entry['content'].encode('utf-8')
        if entry['mode'] == 'sync':
            print(f"  Synchronizing {entry.get('label', 'cached subtitle')} against audio...", flush=True)
            content = synchronizer.sync(content)
        fingerprint = content_fingerprint(content)
        if fingerprint in fingerprints:
            marker.finish_pending(key, fingerprints[fingerprint])
            print('  Identical to an existing alternative; keeping one copy.', flush=True)
            return False
        entry['output'] = content.decode('utf-8-sig')
        entry['target'] = next_output_path(marker.video, entry['hearing_impaired'], language=code).name
        marker.save()
    content = entry['output'].encode('utf-8')
    fingerprint = content_fingerprint(content)
    if fingerprint in fingerprints:
        marker.finish_pending(key, fingerprints[fingerprint])
        return False
    target = marker.video.with_name(entry['target'])
    while os.path.lexists(target):
        if target.is_file() and not target.is_symlink() and target.read_bytes() == content:
            # Recover a completed write interrupted before its marker update.
            break
        target = next_output_path(marker.video, entry['hearing_impaired'], language=code)
        entry['target'] = target.name
        marker.save()
    else:
        # Another process may create this name after the existence check.
        while not write_new(target, content):
            target = next_output_path(marker.video, entry['hearing_impaired'], language=code)
            entry['target'] = target.name
            marker.save()
    marker.finish_pending(key, target)
    fingerprints[fingerprint] = target
    print(f'  Saved {target.name}', flush=True)
    return True


def process_video(path, pool, *, count, minimum, refiners, refiner_configs,
                  categories, skip_wrong_fps=False, dry_run=False, retry_failed=True,
                  retry_short=False):
    if hasattr(pool, 'begin_video'):
        pool.begin_video()
    marker = VideoMarker(path, dry_run=dry_run, targets={'en': count, 'no': 2})
    with SubtitleSynchronizer(path) as synchronizer:
        try:
            return _process_video(
                path, pool, count=count, minimum=minimum, refiners=refiners,
                refiner_configs=refiner_configs, categories=categories,
                skip_wrong_fps=skip_wrong_fps, dry_run=dry_run, synchronizer=synchronizer,
                marker=marker, retry_failed=retry_failed,
                retry_short=retry_short,
            )
        except SyncDependencyError:
            # A missing installation dependency stops the scan. Once installed,
            # the same folder command should resume without a manual retry.
            raise
        except Exception:
            try:
                for code in marker.ready_languages:
                    marker.start_attempt(code)
                finish_attempt(marker, pool)
            except Exception as error:
                print(f'Could not record this attempt: {error}', file=sys.stderr, flush=True)
            raise


def finish_attempt(marker, pool):
    if marker.dry_run:
        return
    quota = getattr(pool, 'quota_exhausted', False)
    marker.record_attempt(quota_exhausted=provider_paused(pool))
    if marker.finished():
        print(f'Subtitles complete ({marker.counts()}).', flush=True)
    elif getattr(pool, 'rate_limited', False):
        print('Paused for a temporary provider rate limit; the next folder scan can resume.',
              flush=True)
    elif quota:
        print('Paused for download allowance; the next folder scan can resume.', flush=True)
    else:
        print(f'Incomplete ({marker.counts()}); automatic retry eligible '
              f'{marker.next_retry_text()}.', flush=True)


def _process_video(path, pool, *, count, minimum, refiners, refiner_configs,
                   categories, synchronizer, marker, skip_wrong_fps=False,
                   dry_run=False, retry_failed=True, retry_short=False):
    print(f'\n{path}', flush=True)
    targets = {'en': count, 'no': 2}
    original_copied = copy_original_subtitle(path, dry_run=dry_run)
    # Finish a journaled save before treating its physical file as a completed
    # slot. This recovers a crash after publication but before the ID update.
    for key, entry in list(marker.data['pending'].items()):
        if 'output' not in entry or 'target' not in entry:
            continue
        published = path.with_name(entry['target'])
        if (published.is_file() and not published.is_symlink()
                and published.read_bytes() == entry['output'].encode('utf-8')):
            marker.finish_pending(key, published)
            print(f'Recovered prior save: {published.name}', flush=True)
    if not marker.finished() or retry_short:
        marker.adopt_numbered()
    if marker.policy_rechecks:
        languages = ', '.join(f'{LANGUAGE_NAMES[code]} '
                             f'{len(marker.files(code))}/{targets[code]}'
                             for code in marker.policy_rechecks)
        reason = 'Automatic retries enabled' if marker.retry_migrated else 'Updated matching/sync rules'
        print(f'{reason}; rechecking missing alternatives: {languages}.', flush=True)
    if marker.finished():
        if marker.adopt_existing or marker.adopted_changed or marker.retry_migrated:
            marker.save()
        print(f'Subtitles already present ({marker.counts()}); skipping.', flush=True)
        return VideoResult(saved=original_copied, candidates=0, kept=len(marker.files()),
                           skipped=not original_copied)
    marker.prepare_retries(force=retry_short)
    if not marker.ready_languages:
        if marker.adopt_existing or marker.adopted_changed or marker.retry_migrated:
            marker.save()
        print(f'Waiting for automatic retry ({marker.counts()}); eligible '
              f'{marker.next_retry_text()}.', flush=True)
        return VideoResult(saved=original_copied, candidates=0, kept=len(marker.files()),
                           skipped=not original_copied)
    marker.data['retry_manually'] = False
    reserved = set()
    migrate_legacy_names(path, marker, dry_run=dry_run, reserved=reserved)
    marker.adopt_numbered()
    kept = len(marker.files())
    total_saved = original_copied
    total_candidates = total_attempts = errors = 0
    pending = {}
    blocked = set()
    for code, target in targets.items():
        if marker.language_finished(code, target):
            print(f'{LANGUAGE_NAMES[code]}: {len(marker.files(code))}/{target} already present.',
                  flush=True)
            continue
        if code not in marker.ready_languages:
            print(f'{LANGUAGE_NAMES[code]}: {len(marker.files(code))}/{target}; '
                  f'automatic retry eligible {marker.next_retry_text(code)}.', flush=True)
            continue
        fingerprints = {content_fingerprint(file.read_bytes()): file for file in marker.files(code)}
        cached = [(key, entry) for key, entry in marker.data['pending'].items()
                  if entry['language'] == code and not marker.rejection_blocks(key)]
        if cached:
            marker.start_attempt(code)
        for key, entry in cached:
            if len(marker.files(code)) >= target:
                break
            if dry_run:
                print(f"Would retry cached {entry.get('label', 'subtitle')} without downloading it.", flush=True)
                continue
            try:
                total_saved += publish_pending(marker, key, synchronizer, fingerprints)
            except SyncDependencyError:
                raise
            except SyncRejected as error:
                marker.reject_pending(key, error)
                print(f'  {error}', flush=True)
            except SyncError as error:
                print(f'  {error} Download retained in the marker for retry.', flush=True)
                errors += 1
                blocked.add(code)
        if code in blocked:
            continue
        if marker.language_finished(code, target):
            print(f'{LANGUAGE_NAMES[code]} already finished; skipping that language.', flush=True)
        elif dry_run and len(marker.files(code)) + len(cached) >= target:
            print(f'{LANGUAGE_NAMES[code]} can be filled from cached downloads; no search needed.', flush=True)
        else:
            pending[code] = target
    # Persist partial progress before searching; a preview never writes this.
    marker.save()
    if not pending:
        print(f'{total_saved} new or recovered files; {kept} existing alternatives kept; '
              'no provider search needed.', flush=True)
        finish_attempt(marker, pool)
        return VideoResult(saved=total_saved, candidates=0, kept=kept,
                           skipped=total_saved == 0 and errors == 0, errors=errors)
    video = scan_media_video(path)
    refine(video, refiners=refiners, refiner_configs=refiner_configs,
           providers=pool.providers, embedded_subtitles=False)
    apply_movie_identity(video, marker.data['movie_identity'])
    if isinstance(video, Movie):
        label = f'{video.title} ({video.year})' if video.year is not None else video.title
        print(f'Searching movie: {label}', flush=True)
    maximum = get_scores(video)['hash']
    search_results = {}
    for code, wanted in pending.items():
        if provider_paused(pool):
            break
        marker.start_attempt(code)
        # Search separately so English pagination cannot crowd Norwegian results
        # out of a provider's result window. Stop before even searching the next
        # language if the preceding download used the last available allowance.
        returned = pool.list_subtitles(video, LANGUAGES[code])
        search_results[code] = returned
        if provider_paused(pool):
            break
        learn_movie_identity(video, returned, marker)
        candidates, mode = select_candidates(video, returned, categories, code)
        if candidates and mode == 'sync':
            if learn_movie_identity(video, [subtitle for _, subtitle in candidates],
                                    marker, allow_title=True):
                candidates, mode = select_candidates(video, returned, categories, code)
        if not candidates:
            returned, candidates, mode = search_movie_title_variants(
                video, pool, marker, returned, categories, code)
            search_results[code] = returned
        if not candidates and isinstance(video, Movie) and not marker.data['movie_identity']:
            # An earlier run may already have all English alternatives, while a
            # franchise-prefixed filename prevents the other language matching.
            # A search in the other language can identify the movie via its hash;
            # this does not download any subtitle or spend download allowance.
            other = 'no' if code == 'en' else 'en'
            reference_results = search_results.get(other)
            if reference_results is None:
                reference_results = pool.list_subtitles(video, LANGUAGES[other])
                search_results[other] = reference_results
            if provider_paused(pool):
                break
            if learn_movie_identity(video, reference_results, marker):
                returned = pool.list_subtitles(video, LANGUAGES[code])
                search_results[code] = returned
                candidates, mode = select_candidates(video, returned, categories, code)
        total_candidates += len(candidates)
        if mode == 'hash':
            print(f'{LANGUAGE_NAMES[code]}: {len(returned)} candidates returned; '
                  f'{len(candidates)} file-hash matches; no synchronization needed.', flush=True)
        else:
            print(f'{LANGUAGE_NAMES[code]}: {len(returned)} candidates returned; '
                  f'{len(candidates)} match this film/episode. No file-hash match.', flush=True)
            print('Fallback: no minimum match-score cutoff; film/episode identity is still checked. '
                  'Candidates will be synchronized with ffsubsync.' if candidates else
                  'No matching film/episode candidates to synchronize; no score cutoff was applied.', flush=True)
            if candidates and not dry_run:
                synchronizer.ensure_ready()
        existing = marker.files(code)
        fingerprints = {content_fingerprint(file.read_bytes()): file for file in existing}
        attempts = saved = 0
        sync_failed = False
        for rank, (score, subtitle) in enumerate(candidates, 1):
            if provider_paused(pool):
                break
            provider, token = subtitle_identity(subtitle)
            target = marker.lookup(provider, token, language=code)
            label = f'#{rank}: {100 * score / maximum:.1f}% {subtitle.provider_name} {subtitle.id}'
            if target is not None and target.is_file() and not target.is_symlink():
                print(f'{label} — already present, keeping it.', flush=True)
                continue
            key = f'{code}:{provider}:{token}'
            if marker.rejection_blocks(key):
                print(f'{label} — rejected under this sync policy; skipping. '
                      f"Reason: {marker.data['rejected'][key]}", flush=True)
                continue
            if attempts + len(existing) >= wanted:
                break
            target = next_output_path(path, subtitle.hearing_impaired, reserved, code)
            if dry_run:
                action = 'would save' if mode == 'hash' else 'would download, sync, and save'
                print(f'{label} — {action} {target.name}', flush=True)
                reserved.add(target)
                attempts += 1
                continue
            print(f'{label} — downloading', flush=True)
            attempts += 1
            if not pool.download_subtitle(subtitle):
                print('  Download failed; existing files are untouched.', flush=True)
                continue
            if not subtitle.convert(output_format='srt', output_encoding='utf-8',
                                    fps=subtitle.fps or video.frame_rate):
                print('  Could not convert to SRT; skipped.', flush=True)
                continue
            content = subtitle.content
            if not content:
                continue
            key = marker.stage(subtitle, code, mode, content)
            try:
                saved += publish_pending(marker, key, synchronizer, fingerprints)
            except SyncDependencyError:
                raise
            except SyncRejected as error:
                marker.reject_pending(key, error)
                print(f'  {error}', flush=True)
            except SyncError as error:
                print(f'  {error} Download retained in the marker for retry.', flush=True)
                sync_failed = True
                errors += 1
                break
        if not dry_run:
            if len(marker.files(code)) >= wanted:
                marker.data['done'][code] = wanted
            else:
                marker.data['done'].pop(code, None)
            marker.save()
        total_saved += saved
        total_attempts += attempts
        if sync_failed:
            break
    if not dry_run:
        print(f'{total_saved} new files; {kept} existing alternatives kept; '
              f'{total_attempts} download attempts.', flush=True)
        finish_attempt(marker, pool)
    return VideoResult(saved=total_saved, candidates=total_candidates, kept=kept,
                       quota_exhausted=getattr(pool, 'quota_exhausted', False),
                       rate_limited=getattr(pool, 'rate_limited', False), errors=errors)


def content_fingerprint(content):
    return hashlib.sha256(content.replace(b'\r\n', b'\n').strip()).digest()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('paths', nargs='*', help='Video files or folders; defaults to the current folder, recursively.')
    parser.add_argument('-c', '--config', type=Path,
                        default=user_config_path('subliminal') / 'subliminal.toml')
    parser.add_argument('-n', '--count', type=int, choices=range(1, 6), default=3,
                        help='English alternatives/download attempts per video (default: 3). Norwegian is fixed at 2.')
    parser.add_argument('-m', '--min-score', type=int, choices=range(101), metavar='0..100',
                        help='Legacy setting; the sync fallback has no minimum match-score cutoff.')
    parser.add_argument('-p', '--provider', action='append', help='Override providers; repeat as needed.')
    parser.add_argument('--dry-run', action='store_true', help='Search and rank; no subtitle downloads or writes.')
    args = parser.parse_args(argv)
    logging.basicConfig(level=logging.WARNING, format='%(levelname)s: %(message)s')
    logging.getLogger('knowit.providers.mkvmerge').addFilter(OptionalMkvmergeWarning())
    try:
        with args.config.expanduser().open(encoding='utf-8') as stream:
            config = tomlkit.parse(stream.read()).unwrap()
        download = config.get('download', {})
        providers = args.provider or download.get('provider') or [
            'opensubtitlescom', 'addic7ed', 'gestdown'
        ]
        providers = [p for p in providers if p not in download.get('ignore_provider', [])]
        # The upstream package still lists this provider, but the service is offline.
        # An explicit -p podnapisi remains available if the service returns.
        if not args.provider and 'podnapisi' in providers:
            print('Skipping Podnapisi: the service is offline.', flush=True)
            providers = [p for p in providers if p != 'podnapisi']
        refiners = [r for r in download.get('refiner', ['metadata', 'hash'])
                    if r not in download.get('ignore_refiner', [])]
        unknown = set(providers) - set(provider_manager.names())
        unknown_refiners = set(refiners) - set(refiner_manager.names())
        if unknown or unknown_refiners or not providers:
            raise ValueError(f'Invalid provider/refiner selection: {sorted(unknown | unknown_refiners)}')
        minimum = args.min_score if args.min_score is not None else download.get('min_score', 90)
        if not isinstance(minimum, int) or not 0 <= minimum <= 100:
            raise ValueError('min_score must be an integer from 0 to 100.')
        # Independent in-memory cache: no changes to the normal CLI's cache/config.
        region.configure('dogpile.cache.memory')
        total = errors = videos = matches = kept = skipped = 0
        stopped_for_quota = False
        stopped_for_rate_limit = False
        explicit_files = {os.path.realpath(Path(raw).expanduser()) for raw in args.paths
                          if Path(raw).expanduser().is_file()}
        print(f'getsubs {SCRIPT_VERSION} — {Path(__file__).resolve()}', flush=True)
        print('PREVIEW: searches only; no subtitle downloads or writes.' if args.dry_run
              else f'Downloading up to {args.count} English and 2 Norwegian alternatives per video; '
                   'existing files are preserved.', flush=True)
        if not args.paths:
            print(f'Scanning current folder and subfolders: {Path.cwd()}', flush=True)
        with QuotaAwarePool(providers=providers, provider_configs=config.get('provider', {})) as pool:
            for path in prioritized_video_paths(args.paths or ['.']):
                videos += 1
                try:
                    result = process_video(
                        path, pool, count=args.count, minimum=minimum, refiners=refiners,
                        refiner_configs=config.get('refiner', {}),
                        categories=download.get('subtitle_categories', 'n,hi'),
                        skip_wrong_fps=download.get('skip_wrong_fps', False),
                        dry_run=args.dry_run,
                        retry_failed=os.path.realpath(path) in explicit_files,
                        retry_short=os.path.realpath(path) in explicit_files,
                    )
                    total += result.saved
                    matches += result.candidates
                    kept += result.kept
                    skipped += result.skipped
                    errors += result.errors
                    if result.quota_exhausted:
                        stopped_for_quota = True
                        break
                    if result.rate_limited:
                        stopped_for_rate_limit = True
                        break
                except SyncDependencyError as error:
                    print(f'Setup required: {error}\nNo further downloads attempted.',
                          file=sys.stderr, flush=True)
                    return 2
                except Exception as error:
                    errors += 1
                    print(f'Error processing {path}: {error}', file=sys.stderr, flush=True)
                    if getattr(pool, 'quota_exhausted', False):
                        stopped_for_quota = True
                        break
                    if getattr(pool, 'rate_limited', False):
                        stopped_for_rate_limit = True
                        break
            failed_providers = set(pool.failed_providers)
            if failed_providers:
                print('Sources reporting errors: ' + ', '.join(sorted(failed_providers)) +
                      '. Results from other sources are retained.', file=sys.stderr, flush=True)
            if stopped_for_quota:
                print('Stopped: OpenSubtitles download allowance exhausted. '
                      'Saved subtitles and progress are kept.', flush=True)
                if getattr(pool, 'quota_reset', None):
                    print(f'Quota resets: {pool.quota_reset}', flush=True)
                print('Run getsubs again after the allowance resets to resume.', flush=True)
            elif stopped_for_rate_limit:
                print('Paused: OpenSubtitles request rate limit. '
                      'Run getsubs again later to resume; this is not the daily download allowance.',
                      flush=True)
        if not videos:
            raise ValueError('No supported video files found.')
        print(f'\nFinished: {videos} videos; {matches} qualifying candidates; '
              f'{total} new subtitle files; {kept} existing alternatives; '
              f'{skipped} videos skipped; {errors} file errors.', flush=True)
        if args.dry_run and not (stopped_for_quota or stopped_for_rate_limit):
            print('Preview complete. Remove --dry-run to download the listed alternatives.', flush=True)
        if stopped_for_quota:
            return 3
        if stopped_for_rate_limit:
            return 4
        # A failed secondary source does not make a useful preview/download a failure.
        useful_result = matches + skipped > 0 if args.dry_run else total + kept + skipped > 0
        return 1 if errors or (failed_providers and not useful_result) else 0
    except (OSError, ValueError, TypeError) as error:
        parser.exit(2, f'Error: {error}\n')


if __name__ == '__main__':
    raise SystemExit(main())
