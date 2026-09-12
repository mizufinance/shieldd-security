# Pinned BINSEC output fixtures

`secure.txt` and `branch-leak.txt` are unedited BINSEC dfe4739 outputs from the
native Linux controls in GitHub Actions run 34673255941. `depth-limit.txt` replays
that run's safe-control core with `-sse-depth 1` using the same pinned BINSEC image.
They exercise real complete, insecure, and incomplete verdict parsing.
