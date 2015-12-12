'format global';

/*!
 * MIT Licensed
 * https://github.com/IntelRealSense/depth-reader-js
 * XDM 1.0 spec: https://software.intel.com/en-us/articles/the-extensible-device-metadata-xdm-specification-version-10
 * Copyright © 2015 Intel Corporation
 */
(function() {
  'use strict';

  var root = this // _window_ if in browser
    , xhrResType
    , Promise
    , XMLHttpRequest
    , DOMParser
    , Canvas
    , Image;

  if ('object' === typeof exports) { // Node.js
    xhrResType     = 'buffer';
    Promise        = require('rsvp').Promise;
    XMLHttpRequest = require('xhr2');
    DOMParser      = require('xmldom').DOMParser;
    Canvas         = require('canvas');
    Image          = Canvas.Image;
  } else { // browser
    xhrResType     = 'arraybuffer';
    Promise        = root.Promise ||
                     root.RSVP.Promise;
    XMLHttpRequest = root.XMLHttpRequest;
    DOMParser      = root.DOMParser;
    Image          = root.Image;
  }

  var DepthReader = function() {
    this._namespaces = {};

    this.isXDM    = false;
    this.revision = 0;
    this.device   = {
      vendor: {
        manufacturer: ''
      , model:        ''
      }
    , pose: {
        latitude:  0
      , longitude: 0
      , altitude:  0
      }
    };
    this.camera = {
      vendor: {
        manufacturer: ''
      , model:        ''
      }
    , pose: {
        positionX:     0
      , positionY:     0
      , positionZ:     0
      , rotationAxisX: 0
      , rotationAxisY: 0
      , rotationAxisZ: 0
      , rotationAngle: 0
      }
    };
    this.perspective = { // XDM
      focalLengthX:    0
    , focalLengthY:    0
    , principalPointX: 0
    , principalPointY: 0
    };
    this.focus = { // Lens Blur
      focalPointX:    0
    , focalPointY:    0
    , focalDistance:  0
    , blurAtInfinity: 0
    };
    this.image = {
      mime: ''
    , data: null // data URI
    };
    this.depth = {
      metric: false // unit is meter if true
    , format: '' // RangeInverse/RangeLinear
    , near:   0
    , far:    0
    , mime:   ''
    , data:   null // data URI
    , raw: {
        mime: ''
      , data: null // data URI
      }
    };
    this.confidence = {
      mime: ''
    , data: null // data URI
    };
  };

  /**
   * parse XDM/LensBlur JPEG given its ArrayBuffer
   * (function is synchronous and returns nothing;
   * exception will be thrown if parsing fails)
   *
   * @param {ArrayBuffer|Buffer} buffer - JPEG image
   */
  DepthReader.prototype.parseFile = function(buffer) {
    var bytes = new Uint8Array(buffer);
    if (bytes[0] !== 0xff ||
        bytes[1] !== 0xd8) { // JPEG start-of-image
      throw new Error('file is not JPEG image');
    }
    var xmpXapXml = ''
      , xmpExtXml = ''
      , payload
      , header
      , i = 0;

    while (-1 < (i = findMarker(bytes, i))) {
      i += 2; // skip marker to segment start

      if ((header = getHeader(bytes, i))) {
        // payload start = segment start + header length
        //               + sizeof word + null-terminator
        // if extension: + 32-byte HasExtendedXMP UUID
        //               +  8-byte "I don't know/care"
        var isXap = xmpXapNS === header
          , extra = header.length + (isXap ? 3 : 43)
          , size  = (bytes[i  ] << 8)
                  +  bytes[i+1]
                      - extra
          , start = i + extra;
        i = start + size;

        payload = baToStr(bytes, start, size);
        if (isXap) {
          xmpXapXml += payload;
        } else {
          xmpExtXml += payload;
        }
      }
    }
    if (this.debug) {
      // expose for inspection
      this.xmpXapXml = xmpXapXml;
      this.xmpExtXml = xmpExtXml;
    }
    var xapDescElt = parseRDF(this, xmpXapXml)
      , extDescElt = parseRDF(this, xmpExtXml)
      , imageNS    =    getNS(this, 'Image');

     this.isXDM = /xdm\.org/.test(imageNS);
    (this.isXDM ? parseXDM : parseLensBlur).call(
      null, this, imageNS, xapDescElt, extDescElt);

    [ this.image
    , this.depth
    , this.depth.raw
    , this.confidence
    ].forEach(makeDataURI);
  };

  function parseXDM(self, imageNS, xapDescElt, extDescElt) {
    /*
    XDM metadata are usually encoded using the Adobe XMP Toolkit,
    but the XMP serializer, for reasons not entirely understood--
    perhaps for compression, sometimes encodes properties as XML
    attributes instead of child elements; so we must handle both
    structural forms.
    */
    var   vendorNS = getNS(self, 'VendorInfo')
      ,  devPoseNS = getNS(self, 'DevicePose')
      ,  camPoseNS = getNS(self, 'CameraPose')
      ,   deviceNS = getNS(self, 'Device')
      ,   cameraNS = getNS(self, 'Camera')
      ,    depthNS = getNS(self, 'DepthMap')
      ,    noiseNS = getNS(self, 'NoiseModel')
      , perspectNS = getNS(self, 'PerspectiveModel');

    var  xdmRevElt = findChild(xapDescElt, deviceNS, 'Revision')
      , devVendElt = findChild(extDescElt, deviceNS, 'VendorInfo') ||
                     findChild(xapDescElt, deviceNS, 'VendorInfo')
      , camVendElt = findChild(extDescElt, cameraNS, 'VendorInfo')
      , devPoseElt = findChild(extDescElt, deviceNS, 'Pose') ||
                     findChild(xapDescElt, deviceNS, 'Pose')
      , camPoseElt = findChild(extDescElt, cameraNS, 'Pose')
      , imagingElt = lastDesc(
                     findChild(extDescElt, cameraNS, 'ImagingModel'))
      ,   imageElt = findChild(extDescElt, cameraNS, 'Image')
      ,  enhDepElt = lastDesc(
                     findChild(extDescElt, cameraNS, 'DepthMap', 0))
      ,  rawDepElt = findChild(extDescElt, cameraNS, 'DepthMap', 1)
      ,  confidElt = findChild( enhDepElt,  noiseNS, 'Reliability');

    self.revision = +attrValue(extDescElt, deviceNS, 'Revision') ||
                   +childValue( xdmRevElt, deviceNS, 'Revision') ||
                    +elemValue( xdmRevElt);

    self.device.vendor.manufacturer = attrValue(devVendElt, vendorNS, 'Manufacturer') ||
                                     childValue(devVendElt, vendorNS, 'Manufacturer');
    self.camera.vendor.manufacturer = attrValue(camVendElt, vendorNS, 'Manufacturer') ||
                                     childValue(camVendElt, vendorNS, 'Manufacturer');
    self.device.vendor.model        = attrValue(devVendElt, vendorNS, 'Model') ||
                                     childValue(devVendElt, vendorNS, 'Model');
    self.camera.vendor.model        = attrValue(camVendElt, vendorNS, 'Model') ||
                                     childValue(camVendElt, vendorNS, 'Model');

    self.device.pose.latitude  = +attrValue(devPoseElt, devPoseNS, 'Latitude') ||
                                +childValue(devPoseElt, devPoseNS, 'Latitude');
    self.device.pose.longitude = +attrValue(devPoseElt, devPoseNS, 'Longitude') ||
                                +childValue(devPoseElt, devPoseNS, 'Longitude');
    self.device.pose.altitude  = +attrValue(devPoseElt, devPoseNS, 'Altitude') ||
                                +childValue(devPoseElt, devPoseNS, 'Altitude');

    self.camera.pose.positionX = +attrValue(camPoseElt, camPoseNS, 'PositionX') ||
                                +childValue(camPoseElt, camPoseNS, 'PositionX');
    self.camera.pose.positionY = +attrValue(camPoseElt, camPoseNS, 'PositionY') ||
                                +childValue(camPoseElt, camPoseNS, 'PositionY');
    self.camera.pose.positionZ = +attrValue(camPoseElt, camPoseNS, 'PositionZ') ||
                                +childValue(camPoseElt, camPoseNS, 'PositionZ');

    self.camera.pose.rotationAxisX = +attrValue(camPoseElt, camPoseNS, 'RotationAxisX') ||
                                    +childValue(camPoseElt, camPoseNS, 'RotationAxisX');
    self.camera.pose.rotationAxisY = +attrValue(camPoseElt, camPoseNS, 'RotationAxisY') ||
                                    +childValue(camPoseElt, camPoseNS, 'RotationAxisY');
    self.camera.pose.rotationAxisZ = +attrValue(camPoseElt, camPoseNS, 'RotationAxisZ') ||
                                    +childValue(camPoseElt, camPoseNS, 'RotationAxisZ');
    self.camera.pose.rotationAngle = +attrValue(camPoseElt, camPoseNS, 'RotationAngle') ||
                                    +childValue(camPoseElt, camPoseNS, 'RotationAngle');

    self.perspective.focalLengthX    = +attrValue(imagingElt, perspectNS, 'FocalLengthX') ||
                                      +childValue(imagingElt, perspectNS, 'FocalLengthX');
    self.perspective.focalLengthY    = +attrValue(imagingElt, perspectNS, 'FocalLengthY') ||
                                      +childValue(imagingElt, perspectNS, 'FocalLengthY');
    self.perspective.principalPointX = +attrValue(imagingElt, perspectNS, 'PrincipalPointX') ||
                                      +childValue(imagingElt, perspectNS, 'PrincipalPointX');
    self.perspective.principalPointY = +attrValue(imagingElt, perspectNS, 'PrincipalPointY') ||
                                      +childValue(imagingElt, perspectNS, 'PrincipalPointY');

    self.depth.metric = parseBool(
                         attrValue(enhDepElt, depthNS, 'Metric') ||
                        childValue(enhDepElt, depthNS, 'Metric'));
    self.depth.format =  attrValue(enhDepElt, depthNS, 'Format') ||
                        childValue(enhDepElt, depthNS, 'Format');
    self.depth.near   = +attrValue(enhDepElt, depthNS, 'Near') ||
                       +childValue(enhDepElt, depthNS, 'Near');
    self.depth.far    = +attrValue(enhDepElt, depthNS, 'Far') ||
                       +childValue(enhDepElt, depthNS, 'Far');

    self.image.mime      = attrValue( imageElt, imageNS, 'Mime') ||
                          childValue( imageElt, imageNS, 'Mime');
    self.depth.mime      = attrValue(enhDepElt, depthNS, 'Mime') ||
                          childValue(enhDepElt, depthNS, 'Mime');
    self.depth.raw.mime  = attrValue(rawDepElt, depthNS, 'Mime') ||
                          childValue(rawDepElt, depthNS, 'Mime');
    self.confidence.mime = attrValue(confidElt, imageNS, 'Mime') ||
                          childValue(confidElt, imageNS, 'Mime');
    self.image.data      = attrValue( imageElt, imageNS, 'Data') ||
                          childValue( imageElt, imageNS, 'Data');
    self.depth.data      = attrValue(enhDepElt, depthNS, 'Data') ||
                          childValue(enhDepElt, depthNS, 'Data');
    self.depth.raw.data  = attrValue(rawDepElt, depthNS, 'Data') ||
                          childValue(rawDepElt, depthNS, 'Data');
    self.confidence.data = attrValue(confidElt, imageNS, 'Data') ||
                          childValue(confidElt, imageNS, 'Data');
  }

  function parseLensBlur(self, imageNS, xapDescElt, extDescElt) {
    var depthNS = getNS(self, 'DepthMap')
      , focusNS = getNS(self, 'Focus');

    self.focus.focalPointX    = +attrValue(xapDescElt, focusNS, 'FocalPointX');
    self.focus.focalPointY    = +attrValue(xapDescElt, focusNS, 'FocalPointY');
    self.focus.focalDistance  = +attrValue(xapDescElt, focusNS, 'FocalDistance');
    self.focus.blurAtInfinity = +attrValue(xapDescElt, focusNS, 'BlurAtInfinity');

    self.depth.format =  attrValue(xapDescElt, depthNS, 'Format');
    self.depth.near   = +attrValue(xapDescElt, depthNS, 'Near');
    self.depth.far    = +attrValue(xapDescElt, depthNS, 'Far');

    self.image.mime = attrValue(xapDescElt, imageNS, 'Mime');
    self.depth.mime = attrValue(xapDescElt, depthNS, 'Mime');
    self.image.data = attrValue(extDescElt, imageNS, 'Data');
    self.depth.data = attrValue(extDescElt, depthNS, 'Data');
  }

  // parse given XML and return x:xmpmeta
  // -> rdf:RDF -> rdf:Description element
  // (also reads namespaces for later use)
  function parseRDF(self, xmpXml) {
    try {
      var parser  = new DOMParser
        , xmlDoc  = parser.parseFromString(xmpXml, 'application/xml')
        , rdfDesc = lastDesc(firstChild(xmlDoc.documentElement));

      readNS(self, rdfDesc);
      return       rdfDesc;
    } catch (err) {
      throw new Error('cannot parse XMP XML');
    }
  }

  // get child rdf:Description;
  // return parent if not found
  function lastDesc(parent) {
    // XDM may contain multiple rdf:Description
    // elements where last contains useful info
    var elts = parent && parent.childNodes || [];

    for (var i = elts.length - 1; i >= 0; i--) {
      if ('rdf:Description' === elts[i].nodeName) {
        return elts[i];
      }
    }
    return parent;
  }

  function firstChild(parent) {
    var elt = parent && parent.firstChild;
    for (; elt && 1 !== elt.nodeType;
           elt = elt.nextSibling) {
      // skip #text node if needed
    }
    return elt || null;
  }

  function findChild(parent, ns, name, index) {
    var elts = parent && parent.getElementsByTagNameNS(ns, name);
    return elts && elts[index|0] || null;
  }

  function childValue(parent, ns, name) {
    return elemValue(findChild(parent, ns, name));
  }

  function elemValue(elt) {
    return elt && elt.textContent || '';
  }

  function attrValue(elt, ns, name) {
    return elt && elt.getAttributeNS(ns, name) || '';
  }

  // make image.data a data URI
  function makeDataURI(image) {
    if (image.mime && image.data) {
      image.data =   'data:'  + image.mime
                 + ';base64,' + image.data;
    }
  }

  /*
  get index of next APP1 marker
  pos: starting index within buf
  return: index; -1 if not found
  */
  function findMarker(buf, pos) {
    for (var i = pos; i < buf.length; i++) {
      if (0xff === buf[i  ] &&
          0xe1 === buf[i+1]) {
        return i;
      }
    }
    return -1;
  }

  /*
  get XMP segment header string
  pos: starting index of segment
  return: header; '' if not found
  */
  function getHeader(arr, pos) {
    pos += 2; // skip segment size
    return hasHeader(xmpXapNS) ? xmpXapNS :
           hasHeader(xmpExtNS) ? xmpExtNS : '';

    function hasHeader(header) {
      var str = baToStr(arr, pos, header.length);
      return header === str;
    }
  }
  var xmpXapNS = 'http://ns.adobe.com/xap/1.0/'
    , xmpExtNS = 'http://ns.adobe.com/xmp/extension/';

  function readNS(self, elt) {
    var nsMap = self._namespaces
      , attrs = elt && elt.attributes || [];

    for (var i = attrs.length - 1; i >= 0; i--) {
      var prefix = attrs[i].name
        , uri    = attrs[i].value;

      if (/^xmlns:/.test(prefix) &&
          /^http:\/\/ns\.(xdm\.org|google\.com)\//.test(uri)) {
        nsMap[prefix.slice(6)] = uri.toLowerCase();
      }
    }
  }

  // name: get namespace with
  //   URI ending in /{name}/
  function getNS(self, name) {
    var nsMap    = self._namespaces
      , prefixes = Object.keys(nsMap);
    name = '/' + name.toLowerCase() + '/';

    for (var i = prefixes.length - 1; i >= 0; i--) {
      var prefix = prefixes[i]
        , uri    = nsMap[prefix]
        , j      = uri.length - name.length;
      if (name === uri.slice(j)) {
        return uri;
      }
    }
    return '';
  }

  // convert sub-Uint8Array to string
  function baToStr(arr, pos, len) {
    arr = arr.subarray(pos, pos + len);
    try {
      return String.fromCharCode.apply(null, arr);
    } catch (err) {
      // workaround PhantomJS bug:
      // https://github.com/ariya/phantomjs/issues/11172
      var i = -1
        , j = arr.length
        , a = new Array(j);
      while (++i < j) {
        a[i] = arr[i];
      }
      return String.fromCharCode.apply(null, a);
    }
  }

  // parse '1'/'true'/'yes'
  function parseBool(str) {
    return !!String(str).match(/^\s*1|true|yes\s*$/i);
  }

  function loadImage(src, img) {
    return new Promise(function(resolve, reject) {
      try {
        if (!img) {
          img = new Image;
        }
        img.onload = function() {
          resolve(img);
        };
        img.onerror = function() {
          reject(new Error('cannot load image'));
        };
        img.src = src;
      } catch (err) {
        reject(err);
      }
    });
  }

  function newCanvas(w, h) {
    if (Canvas) { // Node.js
      return new Canvas(w, h);
    }
    var canvas = document.createElement('canvas');
    canvas.width  = w;
    canvas.height = h;
    return canvas;
  }

  /**
   * load XDM/LensBlur image given JPEG file URL
   * (parseFile() will be invoked automatically)
   *
   * @param {string} fileUrl - URL for XMLHttpRequest
   * @return Promise that will be resolved with _this_
  */
  DepthReader.prototype.loadFile = function(fileUrl) {
    var self = this;

    return new Promise(function(resolve, reject) {
      var xhr = new XMLHttpRequest;
      xhr.responseType = xhrResType;
      xhr.open('GET', fileUrl);

      xhr.onload = function() {
        if (this.response) {
          try { // parsing is synchronous
            self.fileData = this.response;
            self.parseFile.call(self, self.fileData);
            resolve(self);
          } catch (err) {
            reject(err);
          }
        } else {
          var msg = 'cannot load file [' + this.status + ']';
          reject(new Error(msg));
        }
      };
      xhr.send();
    });
  };

  /**
   * normalize the XDM depthmap so that depth
   * values are distributed between 0 and 255
   * (overwrites the original depth.data)
   *
   * @param {string} [func] - name of a registered normalizer
   *                          function (default is "default")
   * @param {object} [opts] - options passed to normalizer
   * @return Promise that will be resolved with modified
   *         depth.data
   */
  DepthReader.prototype.normalizeDepthMap = function(func, opts) {
    var  depth = this.depth;
    if (!depth.data ||
        !this.isXDM) { // not applicable
      return Promise.resolve(depth.data);
    }
    if ('string' !== typeof func) {
      opts = func; func = 'default';
    }
    if ('object' !== typeof opts) {
      // backward compatibility
      // for default normalizer
      opts = {bias: opts};
    } else if (!opts) {
      opts = {bias: 0};
    }

    if (!(func = normalizers[func])) {
      var err  = new Error('normalizer not registered');
      return Promise.reject(err);
    }
    if (depth._origImage) {
      return new Promise(function(resolve, reject) {
        try {
          resolve(normalize(depth._origImage));
        } catch (err) {
          reject(err);
        }
      });
    }
    return loadImage(depth.data)
      .then(function(img) {
        return (depth._origImage = img);
      }).then(normalize);

    function normalize(img) {
      var w      = img.width
        , h      = img.height
        , canvas = newCanvas(w, h)
        , ctx    = canvas.getContext('2d');
      ctx.drawImage(img, 0,0);

      var pixels = ctx.getImageData(0,0, w,h)
        , data   = pixels.data;

      func.call(canvas, data, opts);
      ctx.putImageData(pixels, 0,0);

      data = canvas.toDataURL();
      return (depth.data = data);
    }
  };

  /**
   * register a normalizer function
   * for use by normalizeDepthMap()
   *
   * @param {string}   name - name to identify normalizer
   * @param {function} func - function(data, opts) where
   *        data (Uint8ClampedArray) is ImageData.data
   *        array that should be modified, opts (object)
   *        contains normalizer-specific options, _this_
   *        is Canvas
   */
  DepthReader.registerNormalizer = function(name, func) {
    if ('string'   !== typeof name ||
        'function' !== typeof func) {
      throw new Error('invalid name and/or func');
    }
    normalizers[name] = func;
  };
  var normalizers = {};

  normalizers.default = function(data, opts) {
    // min percent of total depthmap pixels
    // for determining min/max depth values
    var hist   = new Int32Array(256)
      , bias   = opts.bias | 0
      , len    = data.length
      , total  = len / 4
      , thresh = isNaN(+opts.threshold)
               ? 0.1 : +opts.threshold
      , min    = 255
      , max    = 0
      , val,  pcnt
      , norm, prev
      , i, j, spread;

    // get min/max depth values
    for (i = 0; i < len; i += 4) {
      ++hist[val = data[i]];
      if (val > max) {max = val;}
      if (val < min) {min = val;}
    }
    // discard min/max outliers
    for (i = min; i < max; i++) {
      pcnt = hist[i] / total * 100;
      if (thresh <= pcnt) {break;}
    }
    for (j = max; j > min; j--) {
      pcnt = hist[j] / total * 100;
      if (thresh <= pcnt) {break;}
    }
    if (0 < j - i) {
      min = i; max = j;
    }
    spread = 255 / (max - min + 1);
    for (i = 0; i < len; i += 4) {
      if (prev !== (val = data[i])) {
        prev = val;
        // clamp val between adjusted min/max first
        val  = Math.max(0, Math.min(val, max) - min);
        norm = Math.round(val * spread + bias);
      }
      // modify R,G,B not alpha
      for (j = 0; j < 3; j++) {
        data[i + j] = norm;
      }
    }
  };

  if ('object' === typeof exports) {
    module.exports   = DepthReader;
  } else { // browser
    root.DepthReader = DepthReader;
  }
}).call(this);
