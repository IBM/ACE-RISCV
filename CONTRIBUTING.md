# Contributing

It is an open-source project, and we appreciate your help! Contributions are always welcome, both reporting issues and submitting pull requests!

To make contributions to this GitHub repository, please submit a pull request (PR). Please ensure that your new functionality is adequately covered by the regression test suite. In addition, we expect contributors to submit a "Developer's Certificate of Origin" by signing the following form: DCO1.1.txt.

## Reporting issues

Please make sure to include any potentially useful information in the issue, so we can pinpoint the issue faster without going back and forth.

- What commit (SHA) are you running? If this is not the latest SHA on the main branch, please try if the problem persists with the latest version.
- Try to compile the security monitor with debug on. Please include the debug log in your issue description.

Also, please include the following information about your environment, so we can help you faster:
- What version of Linux are you using?
- What version of Qemu are you using?
- What version of Rust are you using?
- What version of RISC-V compiler are you using?
- What are the values of your Qemu configuration?


## Contributing a change

Contributions to this project are [released][released] to the public under the project's [opensource license](LICENSE).
By contributing to this project you agree to the [Developer Certificate of Origin](https://developercertificate.org/) (DCO).
The DCO was created by the Linux Kernel community and is a simple statement that you, as a contributor, wrote or otherwise have the legal right to contribute those changes.

Contributors must _sign-off_ that they adhere to these requirements by adding a `Signed-off-by` line to all commit messages with an email address that matches the commit author:

```
feat: this is my commit message

Signed-off-by: Random J Developer <random@developer.example.org>
```

Git even has a `-s` command line option to append this automatically to your
commit message:

```
$ git commit -s -m 'This is my commit message'
```

## Submitting a pull request

0. [Fork][fork] and clone the repository
1. Create a new branch: `git checkout -b my-branch-name`
2. Make your change, push to your fork and [submit a pull request][pr]
3. Wait for your pull request to be reviewed and merged.

Here are a few things you can do that will increase the likelihood of your pull request being accepted:

- Keep your change as focused as possible. If there are multiple changes you would like to make that are not dependent upon each other, consider submitting them as separate pull requests.
- Write a [good commit message](http://tbaggery.com/2008/04/19/a-note-about-git-commit-messages.html).

## Further Reading

- [Developer Certificate of Origin versus Contributor License Agreements](https://julien.ponge.org/blog/developer-certificate-of-origin-versus-contributor-license-agreements/)
- [The most powerful contributor agreement](https://lwn.net/Articles/592503/)
- [How to Contribute to Open Source](https://opensource.guide/how-to-contribute/)
- [Using Pull Requests](https://help.github.com/articles/about-pull-requests/)
- [GitHub Help](https://help.github.com)