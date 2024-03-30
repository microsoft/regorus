# frozen_string_literal: true

require_relative "lib/regorus/version"

Gem::Specification.new do |spec|
  spec.name = "regorusrb"
  spec.version = Regorus::VERSION
  spec.authors = ["David Marshall"]

  spec.summary = "Ruby bindings for Regorus - a fast, lightweight Rego interpreter written in Rust"
  spec.homepage = "https://github.com/microsoft/regorus/blob/main/bindings/ruby"
  spec.license = "MIT"
  spec.required_ruby_version = ">= 3.0.0"
  spec.required_rubygems_version = ">= 3.3.11"

  spec.metadata["allowed_push_host"] = "TODO: Set to your gem server 'https://example.com'"

  spec.metadata["homepage_uri"] = spec.homepage
  spec.metadata["source_code_uri"] = spec.homepage
  spec.metadata["changelog_uri"] = "#{spec.homepage}/blob/main/bindings/ruby/CHANGELOG.md"
  spec.metadata["rubygems_mfa_required"] = "true"

  # Specify which files should be added to the gem when it is released.
  # The `git ls-files -z` loads the files in the RubyGem that have been added into git.
  gemspec = File.basename(__FILE__)
  spec.files = IO.popen(%w[git ls-files -z], chdir: __dir__, err: IO::NULL) do |ls|
    ls.readlines("\x0", chomp: true).reject do |f|
      (f == gemspec) ||
        f.start_with?(*%w[bin/ test/ spec/ features/ .git .github appveyor Gemfile])
    end
  end

  # Ensure Cargo.lock is included
  spec.files << "../../Cargo.lock" if File.exist?("../../Cargo.lock")

  spec.bindir = "exe"
  spec.executables = spec.files.grep(%r{\Aexe/}) { |f| File.basename(f) }
  spec.require_paths = ["lib"]
  spec.extensions = ["ext/regorusrb/Cargo.toml"]
end
