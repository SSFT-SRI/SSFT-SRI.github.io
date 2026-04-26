## Repository/Website for SRI's Summer School for Formal Techniques (SSFT)

The live page is generated from `index.org` with Emacs Org mode.

### Editing

1. Edit `index.org` or `schedule.org`.
2. Run `make build`.
3. Review the generated `index.html` and `schedule.html`.
4. Commit the Org sources, generated HTML, `style.css`, and any supporting assets.

`make deploy` runs the Org export and a whitespace check. GitHub Pages serves the generated
`index.html` after the changes are committed and pushed.

The GitHub Actions workflow in `.github/workflows/pages.yml` also runs the Org export with
`build-site.el`. Pushes to `org` validate the generated HTML; pushes to the publishing branch
(`main` or `master`) build and deploy the Pages artifact.

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
