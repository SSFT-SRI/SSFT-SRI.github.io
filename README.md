## Repository/Website for SRI's Summer School for Formal Techniques (SSFT)

The live page is generated from `index.org` with Emacs Org mode.

### Editing

1. Edit `index.org`.
2. Run `make build`.
3. Review the generated `index.html`.
4. Commit `index.org`, `index.html`, `style.css`, and any supporting assets.

`make deploy` runs the Org export and a whitespace check. GitHub Pages serves the generated
`index.html` after the changes are committed and pushed.

The GitHub Actions workflow in `.github/workflows/pages.yml` also runs the Org export with
`build-site.el`. Pushes to `org` validate the generated HTML; pushes to the publishing branch
(`main` or `master`) build and deploy the Pages artifact.

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
