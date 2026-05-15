## Repository/Website for SRI's Summer School for Formal Techniques (SSFT)

The live page is generated from Org sources with Emacs Org mode.

### Editing

1. Edit any non-ignored `.org` file.
2. Run `make build`.
3. Review the generated `.html` files.
4. Commit the Org sources, generated HTML, `style.css`, and any supporting assets.

`make build` exports every `.org` file under the repository, except files inside Git-ignored
paths. Add `#+SSFT_EXPORT: nil` to an Org file to keep it out of the generated site.

`make deploy` runs the Org export and a whitespace check. GitHub Pages serves the generated
`index.html` after the changes are committed and pushed.

The GitHub Actions workflow in `.github/workflows/pages.yml` deploys the committed
HTML files. It does not run the Org export; rebuild locally with
`make build` before committing source changes that should appear on the site. Pushes to the
publishing branch (`main` or `master`) package and deploy the Pages artifact.

### Schedule

The timetable is generated from the `Schedule table` in `schedule.org`. Rows use `DATE`, `START`,
`TYPE`, `TITLE`, optional `SPEAKER`, optional `DETAILS`, optional `LOCATION`, optional `DURATION`
in minutes, and optional `NOTE_ID`. `lecture` and `invited` rows default to 90 minutes. Short notes
can go directly in `DETAILS`. Longer notes live under `Schedule notes`; put a note heading's
`CUSTOM_ID` in a row's `NOTE_ID` column to render that note inside the timetable cell.

<!--
**SSFT-SRI/SSFT-SRI** is a ✨ _special_ ✨ repository because its `README.md` (this file) appears on your GitHub profile.

Here are some ideas to get you started:

- 🔭 I’m currently working on ...
- 🌱 I’m currently learning ...
- 👯 I’m looking to collaborate on ...
- 🤔 I’m looking for help with ...
- 💬 Ask me about ...
- 📫 How to reach me: ...
- 😄 Pronouns: ...
- ⚡ Fun fact: ...
-->
