-- Consumer tests: one file that starts with `module`, one plain file that only imports
-- `Rivet`. They see the library differently, so each scenario is checked in both.
import RivetTests.Module
import RivetTests.Plain
