XDM Depth Reader
================

This JavaScript library parses JPEG images in the XDM (eXtensible Device Metadata)
format, which succeeds the Google Lens Blur format generated by the Google Camera
app (it can also read the Lens Blur format as it maintains backward compatibility).

The XDM 1.0 spec was jointly developed by Intel and Google, and is available on the
[Intel Developer Zone](https://software.intel.com/en-us/articles/the-extensible-device-metadata-xdm-specification-version-10).

:exclamation: This library does not currently parse all metadata described by the
spec. However, it's hoped that this project will evolve into a generic reader and
possibly a writer as well in the near future.

This library may be used in both browser and Node.js projects, but some tests fail
if run inside PhantomJS.

## Dependencies

 - [RSVP.js](https://github.com/tildeio/rsvp.js) *(polyfill for Promise)*
 - [XMLDOM](https://github.com/jindw/xmldom) *(polyfill for DOMParser in Node.js)*
 - [node-xhr2](https://github.com/pwnall/node-xhr2) *(polyfill for XMLHttpRequest in Node.js)*
 - [node-canvas](https://github.com/Automattic/node-canvas) *(polyfill for HTML5 canvas in Node.js)*

## Installation

Unless previously installed, you'll need the `Cairo` graphics library.
Follow these [installation instructions](https://github.com/LearnBoost/node-canvas/wiki/_pages)
before continuing.

If you are having trouble compiling `Cairo` or installing the `node-canvas`
module on **Windows**, you can, alternatively, download a snapshot of the
[node_modules](http://storage.realsense.photo/projects/depth-reader-js/node_modules_windows.zip)
folder.

    bower install depth-reader --save

*or*

    npm install depth-reader --save

## Usage

*Browser:*

    <script src="vendor/rsvp.js"></script>
    <script src="depth-reader.js"></script>

*Node.js:*

    var DepthReader = require('./depth-reader'),
        Image       = require('canvas').Image;

Example:

    var fileUrl = 'http://localhost/images/depth.jpg';
    new DepthReader().loadFile(fileUrl)
        .then(function(reader)
        {
            var rgbImage   = new Image(),
                depthImage = new Image();

            rgbImage.src = reader.image.data;
            console.log('RGB image dimensions:',
                rgbImage.width + 'x' + rgbImage.height);

            if (reader.isXDM) {
              // normalize depth values between 1-255
              // and shift them by 64 to boost effect
              reader.normalizeDepthmap(64);
            }
            depthImage.src = reader.depth.data;
            console.log('Depthmap image dimensions:',
                depthImage.width + 'x' + depthImage.height);
        })
        .catch(function(error) {
            console.error('loading failed:', error);
        });

## Development

To contribute to the development of this package and to run the
unit tests, you'll need to install the dev dependencies first:

    npm install

Rebuild the minified release after your changes have been tested:

    grunt build

## Tests

Install global dependencies:

    npm install -g grunt mocha

Run Node.js tests in the console and browser tests in a web page:

    npm start

Print depthmap information (run HTTP server in separate console):

    grunt serve
    node test/info

## Authors

  - Erhhung Yuan <erhhung.yuan@intel.com>

## License

The MIT License

Copyright (c)2015 Intel Corporation
