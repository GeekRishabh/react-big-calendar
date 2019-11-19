;(function(global, factory) {
  typeof exports === 'object' && typeof module !== 'undefined'
    ? factory(exports, require('react'), require('react-dom'))
    : typeof define === 'function' && define.amd
    ? define(['exports', 'react', 'react-dom'], factory)
    : ((global = global || self),
      factory((global.ReactBigCalendar = {}), global.React, global.ReactDOM))
})(this, function(exports, React, ReactDOM) {
  'use strict'

  var React__default = 'default' in React ? React['default'] : React
  var ReactDOM__default = 'default' in ReactDOM ? ReactDOM['default'] : ReactDOM

  function NoopWrapper(props) {
    return props.children
  }

  function _extends() {
    _extends =
      Object.assign ||
      function(target) {
        for (var i = 1; i < arguments.length; i++) {
          var source = arguments[i]

          for (var key in source) {
            if (Object.prototype.hasOwnProperty.call(source, key)) {
              target[key] = source[key]
            }
          }
        }

        return target
      }

    return _extends.apply(this, arguments)
  }

  function _objectWithoutPropertiesLoose(source, excluded) {
    if (source == null) return {}
    var target = {}
    var sourceKeys = Object.keys(source)
    var key, i

    for (i = 0; i < sourceKeys.length; i++) {
      key = sourceKeys[i]
      if (excluded.indexOf(key) >= 0) continue
      target[key] = source[key]
    }

    return target
  }

  function _inheritsLoose(subClass, superClass) {
    subClass.prototype = Object.create(superClass.prototype)
    subClass.prototype.constructor = subClass
    subClass.__proto__ = superClass
  }

  function unwrapExports(x) {
    return x &&
      x.__esModule &&
      Object.prototype.hasOwnProperty.call(x, 'default')
      ? x['default']
      : x
  }

  function createCommonjsModule(fn, module) {
    return (
      (module = { exports: {} }), fn(module, module.exports), module.exports
    )
  }

  var reactIs_production_min = createCommonjsModule(function(module, exports) {
    Object.defineProperty(exports, '__esModule', { value: !0 })
    var b = 'function' === typeof Symbol && Symbol.for,
      c = b ? Symbol.for('react.element') : 60103,
      d = b ? Symbol.for('react.portal') : 60106,
      e = b ? Symbol.for('react.fragment') : 60107,
      f = b ? Symbol.for('react.strict_mode') : 60108,
      g = b ? Symbol.for('react.profiler') : 60114,
      h = b ? Symbol.for('react.provider') : 60109,
      k = b ? Symbol.for('react.context') : 60110,
      l = b ? Symbol.for('react.async_mode') : 60111,
      m = b ? Symbol.for('react.concurrent_mode') : 60111,
      n = b ? Symbol.for('react.forward_ref') : 60112,
      p = b ? Symbol.for('react.suspense') : 60113,
      q = b ? Symbol.for('react.suspense_list') : 60120,
      r = b ? Symbol.for('react.memo') : 60115,
      t = b ? Symbol.for('react.lazy') : 60116,
      v = b ? Symbol.for('react.fundamental') : 60117,
      w = b ? Symbol.for('react.responder') : 60118
    function x(a) {
      if ('object' === typeof a && null !== a) {
        var u = a.$$typeof
        switch (u) {
          case c:
            switch (((a = a.type), a)) {
              case l:
              case m:
              case e:
              case g:
              case f:
              case p:
                return a
              default:
                switch (((a = a && a.$$typeof), a)) {
                  case k:
                  case n:
                  case h:
                    return a
                  default:
                    return u
                }
            }
          case t:
          case r:
          case d:
            return u
        }
      }
    }
    function y(a) {
      return x(a) === m
    }
    exports.typeOf = x
    exports.AsyncMode = l
    exports.ConcurrentMode = m
    exports.ContextConsumer = k
    exports.ContextProvider = h
    exports.Element = c
    exports.ForwardRef = n
    exports.Fragment = e
    exports.Lazy = t
    exports.Memo = r
    exports.Portal = d
    exports.Profiler = g
    exports.StrictMode = f
    exports.Suspense = p
    exports.isValidElementType = function(a) {
      return (
        'string' === typeof a ||
        'function' === typeof a ||
        a === e ||
        a === m ||
        a === g ||
        a === f ||
        a === p ||
        a === q ||
        ('object' === typeof a &&
          null !== a &&
          (a.$$typeof === t ||
            a.$$typeof === r ||
            a.$$typeof === h ||
            a.$$typeof === k ||
            a.$$typeof === n ||
            a.$$typeof === v ||
            a.$$typeof === w))
      )
    }
    exports.isAsyncMode = function(a) {
      return y(a) || x(a) === l
    }
    exports.isConcurrentMode = y
    exports.isContextConsumer = function(a) {
      return x(a) === k
    }
    exports.isContextProvider = function(a) {
      return x(a) === h
    }
    exports.isElement = function(a) {
      return 'object' === typeof a && null !== a && a.$$typeof === c
    }
    exports.isForwardRef = function(a) {
      return x(a) === n
    }
    exports.isFragment = function(a) {
      return x(a) === e
    }
    exports.isLazy = function(a) {
      return x(a) === t
    }
    exports.isMemo = function(a) {
      return x(a) === r
    }
    exports.isPortal = function(a) {
      return x(a) === d
    }
    exports.isProfiler = function(a) {
      return x(a) === g
    }
    exports.isStrictMode = function(a) {
      return x(a) === f
    }
    exports.isSuspense = function(a) {
      return x(a) === p
    }
  })

  unwrapExports(reactIs_production_min)
  var reactIs_production_min_1 = reactIs_production_min.typeOf
  var reactIs_production_min_2 = reactIs_production_min.AsyncMode
  var reactIs_production_min_3 = reactIs_production_min.ConcurrentMode
  var reactIs_production_min_4 = reactIs_production_min.ContextConsumer
  var reactIs_production_min_5 = reactIs_production_min.ContextProvider
  var reactIs_production_min_6 = reactIs_production_min.Element
  var reactIs_production_min_7 = reactIs_production_min.ForwardRef
  var reactIs_production_min_8 = reactIs_production_min.Fragment
  var reactIs_production_min_9 = reactIs_production_min.Lazy
  var reactIs_production_min_10 = reactIs_production_min.Memo
  var reactIs_production_min_11 = reactIs_production_min.Portal
  var reactIs_production_min_12 = reactIs_production_min.Profiler
  var reactIs_production_min_13 = reactIs_production_min.StrictMode
  var reactIs_production_min_14 = reactIs_production_min.Suspense
  var reactIs_production_min_15 = reactIs_production_min.isValidElementType
  var reactIs_production_min_16 = reactIs_production_min.isAsyncMode
  var reactIs_production_min_17 = reactIs_production_min.isConcurrentMode
  var reactIs_production_min_18 = reactIs_production_min.isContextConsumer
  var reactIs_production_min_19 = reactIs_production_min.isContextProvider
  var reactIs_production_min_20 = reactIs_production_min.isElement
  var reactIs_production_min_21 = reactIs_production_min.isForwardRef
  var reactIs_production_min_22 = reactIs_production_min.isFragment
  var reactIs_production_min_23 = reactIs_production_min.isLazy
  var reactIs_production_min_24 = reactIs_production_min.isMemo
  var reactIs_production_min_25 = reactIs_production_min.isPortal
  var reactIs_production_min_26 = reactIs_production_min.isProfiler
  var reactIs_production_min_27 = reactIs_production_min.isStrictMode
  var reactIs_production_min_28 = reactIs_production_min.isSuspense

  var reactIs_development = createCommonjsModule(function(module, exports) {
    {
      ;(function() {
        Object.defineProperty(exports, '__esModule', { value: true })

        // The Symbol used to tag the ReactElement-like types. If there is no native Symbol
        // nor polyfill, then a plain number is used for performance.
        var hasSymbol = typeof Symbol === 'function' && Symbol.for

        var REACT_ELEMENT_TYPE = hasSymbol
          ? Symbol.for('react.element')
          : 0xeac7
        var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca
        var REACT_FRAGMENT_TYPE = hasSymbol
          ? Symbol.for('react.fragment')
          : 0xeacb
        var REACT_STRICT_MODE_TYPE = hasSymbol
          ? Symbol.for('react.strict_mode')
          : 0xeacc
        var REACT_PROFILER_TYPE = hasSymbol
          ? Symbol.for('react.profiler')
          : 0xead2
        var REACT_PROVIDER_TYPE = hasSymbol
          ? Symbol.for('react.provider')
          : 0xeacd
        var REACT_CONTEXT_TYPE = hasSymbol
          ? Symbol.for('react.context')
          : 0xeace
        // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
        // (unstable) APIs that have been removed. Can we remove the symbols?
        var REACT_ASYNC_MODE_TYPE = hasSymbol
          ? Symbol.for('react.async_mode')
          : 0xeacf
        var REACT_CONCURRENT_MODE_TYPE = hasSymbol
          ? Symbol.for('react.concurrent_mode')
          : 0xeacf
        var REACT_FORWARD_REF_TYPE = hasSymbol
          ? Symbol.for('react.forward_ref')
          : 0xead0
        var REACT_SUSPENSE_TYPE = hasSymbol
          ? Symbol.for('react.suspense')
          : 0xead1
        var REACT_SUSPENSE_LIST_TYPE = hasSymbol
          ? Symbol.for('react.suspense_list')
          : 0xead8
        var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3
        var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4
        var REACT_FUNDAMENTAL_TYPE = hasSymbol
          ? Symbol.for('react.fundamental')
          : 0xead5
        var REACT_RESPONDER_TYPE = hasSymbol
          ? Symbol.for('react.responder')
          : 0xead6

        function isValidElementType(type) {
          return (
            typeof type === 'string' ||
            typeof type === 'function' ||
            // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
            type === REACT_FRAGMENT_TYPE ||
            type === REACT_CONCURRENT_MODE_TYPE ||
            type === REACT_PROFILER_TYPE ||
            type === REACT_STRICT_MODE_TYPE ||
            type === REACT_SUSPENSE_TYPE ||
            type === REACT_SUSPENSE_LIST_TYPE ||
            (typeof type === 'object' &&
              type !== null &&
              (type.$$typeof === REACT_LAZY_TYPE ||
                type.$$typeof === REACT_MEMO_TYPE ||
                type.$$typeof === REACT_PROVIDER_TYPE ||
                type.$$typeof === REACT_CONTEXT_TYPE ||
                type.$$typeof === REACT_FORWARD_REF_TYPE ||
                type.$$typeof === REACT_FUNDAMENTAL_TYPE ||
                type.$$typeof === REACT_RESPONDER_TYPE))
          )
        }

        /**
         * Forked from fbjs/warning:
         * https://github.com/facebook/fbjs/blob/e66ba20ad5be433eb54423f2b097d829324d9de6/packages/fbjs/src/__forks__/warning.js
         *
         * Only change is we use console.warn instead of console.error,
         * and do nothing when 'console' is not supported.
         * This really simplifies the code.
         * ---
         * Similar to invariant but only logs a warning if the condition is not met.
         * This can be used to log issues in development environments in critical
         * paths. Removing the logging code for production environments will keep the
         * same logic and follow the same code paths.
         */

        var lowPriorityWarning = function() {}

        {
          var printWarning = function(format) {
            for (
              var _len = arguments.length,
                args = Array(_len > 1 ? _len - 1 : 0),
                _key = 1;
              _key < _len;
              _key++
            ) {
              args[_key - 1] = arguments[_key]
            }

            var argIndex = 0
            var message =
              'Warning: ' +
              format.replace(/%s/g, function() {
                return args[argIndex++]
              })
            if (typeof console !== 'undefined') {
              console.warn(message)
            }
            try {
              // --- Welcome to debugging React ---
              // This error was thrown as a convenience so that you can use this stack
              // to find the callsite that caused this warning to fire.
              throw new Error(message)
            } catch (x) {}
          }

          lowPriorityWarning = function(condition, format) {
            if (format === undefined) {
              throw new Error(
                '`lowPriorityWarning(condition, format, ...args)` requires a warning ' +
                  'message argument'
              )
            }
            if (!condition) {
              for (
                var _len2 = arguments.length,
                  args = Array(_len2 > 2 ? _len2 - 2 : 0),
                  _key2 = 2;
                _key2 < _len2;
                _key2++
              ) {
                args[_key2 - 2] = arguments[_key2]
              }

              printWarning.apply(undefined, [format].concat(args))
            }
          }
        }

        var lowPriorityWarning$1 = lowPriorityWarning

        function typeOf(object) {
          if (typeof object === 'object' && object !== null) {
            var $$typeof = object.$$typeof
            switch ($$typeof) {
              case REACT_ELEMENT_TYPE:
                var type = object.type

                switch (type) {
                  case REACT_ASYNC_MODE_TYPE:
                  case REACT_CONCURRENT_MODE_TYPE:
                  case REACT_FRAGMENT_TYPE:
                  case REACT_PROFILER_TYPE:
                  case REACT_STRICT_MODE_TYPE:
                  case REACT_SUSPENSE_TYPE:
                    return type
                  default:
                    var $$typeofType = type && type.$$typeof

                    switch ($$typeofType) {
                      case REACT_CONTEXT_TYPE:
                      case REACT_FORWARD_REF_TYPE:
                      case REACT_PROVIDER_TYPE:
                        return $$typeofType
                      default:
                        return $$typeof
                    }
                }
              case REACT_LAZY_TYPE:
              case REACT_MEMO_TYPE:
              case REACT_PORTAL_TYPE:
                return $$typeof
            }
          }

          return undefined
        }

        // AsyncMode is deprecated along with isAsyncMode
        var AsyncMode = REACT_ASYNC_MODE_TYPE
        var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE
        var ContextConsumer = REACT_CONTEXT_TYPE
        var ContextProvider = REACT_PROVIDER_TYPE
        var Element = REACT_ELEMENT_TYPE
        var ForwardRef = REACT_FORWARD_REF_TYPE
        var Fragment = REACT_FRAGMENT_TYPE
        var Lazy = REACT_LAZY_TYPE
        var Memo = REACT_MEMO_TYPE
        var Portal = REACT_PORTAL_TYPE
        var Profiler = REACT_PROFILER_TYPE
        var StrictMode = REACT_STRICT_MODE_TYPE
        var Suspense = REACT_SUSPENSE_TYPE

        var hasWarnedAboutDeprecatedIsAsyncMode = false

        // AsyncMode should be deprecated
        function isAsyncMode(object) {
          {
            if (!hasWarnedAboutDeprecatedIsAsyncMode) {
              hasWarnedAboutDeprecatedIsAsyncMode = true
              lowPriorityWarning$1(
                false,
                'The ReactIs.isAsyncMode() alias has been deprecated, ' +
                  'and will be removed in React 17+. Update your code to use ' +
                  'ReactIs.isConcurrentMode() instead. It has the exact same API.'
              )
            }
          }
          return (
            isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE
          )
        }
        function isConcurrentMode(object) {
          return typeOf(object) === REACT_CONCURRENT_MODE_TYPE
        }
        function isContextConsumer(object) {
          return typeOf(object) === REACT_CONTEXT_TYPE
        }
        function isContextProvider(object) {
          return typeOf(object) === REACT_PROVIDER_TYPE
        }
        function isElement(object) {
          return (
            typeof object === 'object' &&
            object !== null &&
            object.$$typeof === REACT_ELEMENT_TYPE
          )
        }
        function isForwardRef(object) {
          return typeOf(object) === REACT_FORWARD_REF_TYPE
        }
        function isFragment(object) {
          return typeOf(object) === REACT_FRAGMENT_TYPE
        }
        function isLazy(object) {
          return typeOf(object) === REACT_LAZY_TYPE
        }
        function isMemo(object) {
          return typeOf(object) === REACT_MEMO_TYPE
        }
        function isPortal(object) {
          return typeOf(object) === REACT_PORTAL_TYPE
        }
        function isProfiler(object) {
          return typeOf(object) === REACT_PROFILER_TYPE
        }
        function isStrictMode(object) {
          return typeOf(object) === REACT_STRICT_MODE_TYPE
        }
        function isSuspense(object) {
          return typeOf(object) === REACT_SUSPENSE_TYPE
        }

        exports.typeOf = typeOf
        exports.AsyncMode = AsyncMode
        exports.ConcurrentMode = ConcurrentMode
        exports.ContextConsumer = ContextConsumer
        exports.ContextProvider = ContextProvider
        exports.Element = Element
        exports.ForwardRef = ForwardRef
        exports.Fragment = Fragment
        exports.Lazy = Lazy
        exports.Memo = Memo
        exports.Portal = Portal
        exports.Profiler = Profiler
        exports.StrictMode = StrictMode
        exports.Suspense = Suspense
        exports.isValidElementType = isValidElementType
        exports.isAsyncMode = isAsyncMode
        exports.isConcurrentMode = isConcurrentMode
        exports.isContextConsumer = isContextConsumer
        exports.isContextProvider = isContextProvider
        exports.isElement = isElement
        exports.isForwardRef = isForwardRef
        exports.isFragment = isFragment
        exports.isLazy = isLazy
        exports.isMemo = isMemo
        exports.isPortal = isPortal
        exports.isProfiler = isProfiler
        exports.isStrictMode = isStrictMode
        exports.isSuspense = isSuspense
      })()
    }
  })

  unwrapExports(reactIs_development)
  var reactIs_development_1 = reactIs_development.typeOf
  var reactIs_development_2 = reactIs_development.AsyncMode
  var reactIs_development_3 = reactIs_development.ConcurrentMode
  var reactIs_development_4 = reactIs_development.ContextConsumer
  var reactIs_development_5 = reactIs_development.ContextProvider
  var reactIs_development_6 = reactIs_development.Element
  var reactIs_development_7 = reactIs_development.ForwardRef
  var reactIs_development_8 = reactIs_development.Fragment
  var reactIs_development_9 = reactIs_development.Lazy
  var reactIs_development_10 = reactIs_development.Memo
  var reactIs_development_11 = reactIs_development.Portal
  var reactIs_development_12 = reactIs_development.Profiler
  var reactIs_development_13 = reactIs_development.StrictMode
  var reactIs_development_14 = reactIs_development.Suspense
  var reactIs_development_15 = reactIs_development.isValidElementType
  var reactIs_development_16 = reactIs_development.isAsyncMode
  var reactIs_development_17 = reactIs_development.isConcurrentMode
  var reactIs_development_18 = reactIs_development.isContextConsumer
  var reactIs_development_19 = reactIs_development.isContextProvider
  var reactIs_development_20 = reactIs_development.isElement
  var reactIs_development_21 = reactIs_development.isForwardRef
  var reactIs_development_22 = reactIs_development.isFragment
  var reactIs_development_23 = reactIs_development.isLazy
  var reactIs_development_24 = reactIs_development.isMemo
  var reactIs_development_25 = reactIs_development.isPortal
  var reactIs_development_26 = reactIs_development.isProfiler
  var reactIs_development_27 = reactIs_development.isStrictMode
  var reactIs_development_28 = reactIs_development.isSuspense

  var reactIs = createCommonjsModule(function(module) {
    {
      module.exports = reactIs_development
    }
  })

  /*
  object-assign
  (c) Sindre Sorhus
  @license MIT
  */
  /* eslint-disable no-unused-vars */
  var getOwnPropertySymbols = Object.getOwnPropertySymbols
  var hasOwnProperty = Object.prototype.hasOwnProperty
  var propIsEnumerable = Object.prototype.propertyIsEnumerable

  function toObject(val) {
    if (val === null || val === undefined) {
      throw new TypeError(
        'Object.assign cannot be called with null or undefined'
      )
    }

    return Object(val)
  }

  function shouldUseNative() {
    try {
      if (!Object.assign) {
        return false
      }

      // Detect buggy property enumeration order in older V8 versions.

      // https://bugs.chromium.org/p/v8/issues/detail?id=4118
      var test1 = new String('abc') // eslint-disable-line no-new-wrappers
      test1[5] = 'de'
      if (Object.getOwnPropertyNames(test1)[0] === '5') {
        return false
      }

      // https://bugs.chromium.org/p/v8/issues/detail?id=3056
      var test2 = {}
      for (var i = 0; i < 10; i++) {
        test2['_' + String.fromCharCode(i)] = i
      }
      var order2 = Object.getOwnPropertyNames(test2).map(function(n) {
        return test2[n]
      })
      if (order2.join('') !== '0123456789') {
        return false
      }

      // https://bugs.chromium.org/p/v8/issues/detail?id=3056
      var test3 = {}
      'abcdefghijklmnopqrst'.split('').forEach(function(letter) {
        test3[letter] = letter
      })
      if (
        Object.keys(Object.assign({}, test3)).join('') !==
        'abcdefghijklmnopqrst'
      ) {
        return false
      }

      return true
    } catch (err) {
      // We don't expect any of the above to throw, but better to be safe.
      return false
    }
  }

  var objectAssign = shouldUseNative()
    ? Object.assign
    : function(target, source) {
        var from
        var to = toObject(target)
        var symbols

        for (var s = 1; s < arguments.length; s++) {
          from = Object(arguments[s])

          for (var key in from) {
            if (hasOwnProperty.call(from, key)) {
              to[key] = from[key]
            }
          }

          if (getOwnPropertySymbols) {
            symbols = getOwnPropertySymbols(from)
            for (var i = 0; i < symbols.length; i++) {
              if (propIsEnumerable.call(from, symbols[i])) {
                to[symbols[i]] = from[symbols[i]]
              }
            }
          }
        }

        return to
      }

  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED'

  var ReactPropTypesSecret_1 = ReactPropTypesSecret

  var printWarning = function() {}

  {
    var ReactPropTypesSecret$1 = ReactPropTypesSecret_1
    var loggedTypeFailures = {}
    var has = Function.call.bind(Object.prototype.hasOwnProperty)

    printWarning = function(text) {
      var message = 'Warning: ' + text
      if (typeof console !== 'undefined') {
        console.error(message)
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message)
      } catch (x) {}
    }
  }

  /**
   * Assert that the values match with the type specs.
   * Error messages are memorized and will only be shown once.
   *
   * @param {object} typeSpecs Map of name to a ReactPropType
   * @param {object} values Runtime values that need to be type-checked
   * @param {string} location e.g. "prop", "context", "child context"
   * @param {string} componentName Name of the component for error messages.
   * @param {?Function} getStack Returns the component stack.
   * @private
   */
  function checkPropTypes(
    typeSpecs,
    values,
    location,
    componentName,
    getStack
  ) {
    {
      for (var typeSpecName in typeSpecs) {
        if (has(typeSpecs, typeSpecName)) {
          var error
          // Prop type validation may throw. In case they do, we don't want to
          // fail the render phase where it didn't fail before. So we log it.
          // After these have been cleaned up, we'll let them throw.
          try {
            // This is intentionally an invariant that gets caught. It's the same
            // behavior as without this statement except with a better message.
            if (typeof typeSpecs[typeSpecName] !== 'function') {
              var err = Error(
                (componentName || 'React class') +
                  ': ' +
                  location +
                  ' type `' +
                  typeSpecName +
                  '` is invalid; ' +
                  'it must be a function, usually from the `prop-types` package, but received `' +
                  typeof typeSpecs[typeSpecName] +
                  '`.'
              )
              err.name = 'Invariant Violation'
              throw err
            }
            error = typeSpecs[typeSpecName](
              values,
              typeSpecName,
              componentName,
              location,
              null,
              ReactPropTypesSecret$1
            )
          } catch (ex) {
            error = ex
          }
          if (error && !(error instanceof Error)) {
            printWarning(
              (componentName || 'React class') +
                ': type specification of ' +
                location +
                ' `' +
                typeSpecName +
                '` is invalid; the type checker ' +
                'function must return `null` or an `Error` but returned a ' +
                typeof error +
                '. ' +
                'You may have forgotten to pass an argument to the type checker ' +
                'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
                'shape all require an argument).'
            )
          }
          if (
            error instanceof Error &&
            !(error.message in loggedTypeFailures)
          ) {
            // Only monitor this failure once because there tends to be a lot of the
            // same error.
            loggedTypeFailures[error.message] = true

            var stack = getStack ? getStack() : ''

            printWarning(
              'Failed ' +
                location +
                ' type: ' +
                error.message +
                (stack != null ? stack : '')
            )
          }
        }
      }
    }
  }

  /**
   * Resets warning cache when testing.
   *
   * @private
   */
  checkPropTypes.resetWarningCache = function() {
    {
      loggedTypeFailures = {}
    }
  }

  var checkPropTypes_1 = checkPropTypes

  var has$1 = Function.call.bind(Object.prototype.hasOwnProperty)
  var printWarning$1 = function() {}

  {
    printWarning$1 = function(text) {
      var message = 'Warning: ' + text
      if (typeof console !== 'undefined') {
        console.error(message)
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message)
      } catch (x) {}
    }
  }

  function emptyFunctionThatReturnsNull() {
    return null
  }

  var factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
    /* global Symbol */
    var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator
    var FAUX_ITERATOR_SYMBOL = '@@iterator' // Before Symbol spec.

    /**
     * Returns the iterator method function contained on the iterable object.
     *
     * Be sure to invoke the function with the iterable as context:
     *
     *     var iteratorFn = getIteratorFn(myIterable);
     *     if (iteratorFn) {
     *       var iterator = iteratorFn.call(myIterable);
     *       ...
     *     }
     *
     * @param {?object} maybeIterable
     * @return {?function}
     */
    function getIteratorFn(maybeIterable) {
      var iteratorFn =
        maybeIterable &&
        ((ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL]) ||
          maybeIterable[FAUX_ITERATOR_SYMBOL])
      if (typeof iteratorFn === 'function') {
        return iteratorFn
      }
    }

    /**
     * Collection of methods that allow declaration and validation of props that are
     * supplied to React components. Example usage:
     *
     *   var Props = require('ReactPropTypes');
     *   var MyArticle = React.createClass({
     *     propTypes: {
     *       // An optional string prop named "description".
     *       description: Props.string,
     *
     *       // A required enum prop named "category".
     *       category: Props.oneOf(['News','Photos']).isRequired,
     *
     *       // A prop named "dialog" that requires an instance of Dialog.
     *       dialog: Props.instanceOf(Dialog).isRequired
     *     },
     *     render: function() { ... }
     *   });
     *
     * A more formal specification of how these methods are used:
     *
     *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
     *   decl := ReactPropTypes.{type}(.isRequired)?
     *
     * Each and every declaration produces a function with the same signature. This
     * allows the creation of custom validation functions. For example:
     *
     *  var MyLink = React.createClass({
     *    propTypes: {
     *      // An optional string or URI prop named "href".
     *      href: function(props, propName, componentName) {
     *        var propValue = props[propName];
     *        if (propValue != null && typeof propValue !== 'string' &&
     *            !(propValue instanceof URI)) {
     *          return new Error(
     *            'Expected a string or an URI for ' + propName + ' in ' +
     *            componentName
     *          );
     *        }
     *      }
     *    },
     *    render: function() {...}
     *  });
     *
     * @internal
     */

    var ANONYMOUS = '<<anonymous>>'

    // Important!
    // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
    var ReactPropTypes = {
      array: createPrimitiveTypeChecker('array'),
      bool: createPrimitiveTypeChecker('boolean'),
      func: createPrimitiveTypeChecker('function'),
      number: createPrimitiveTypeChecker('number'),
      object: createPrimitiveTypeChecker('object'),
      string: createPrimitiveTypeChecker('string'),
      symbol: createPrimitiveTypeChecker('symbol'),

      any: createAnyTypeChecker(),
      arrayOf: createArrayOfTypeChecker,
      element: createElementTypeChecker(),
      elementType: createElementTypeTypeChecker(),
      instanceOf: createInstanceTypeChecker,
      node: createNodeChecker(),
      objectOf: createObjectOfTypeChecker,
      oneOf: createEnumTypeChecker,
      oneOfType: createUnionTypeChecker,
      shape: createShapeTypeChecker,
      exact: createStrictShapeTypeChecker,
    }

    /**
     * inlined Object.is polyfill to avoid requiring consumers ship their own
     * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
     */
    /*eslint-disable no-self-compare*/
    function is(x, y) {
      // SameValue algorithm
      if (x === y) {
        // Steps 1-5, 7-10
        // Steps 6.b-6.e: +0 != -0
        return x !== 0 || 1 / x === 1 / y
      } else {
        // Step 6.a: NaN == NaN
        return x !== x && y !== y
      }
    }
    /*eslint-enable no-self-compare*/

    /**
     * We use an Error-like object for backward compatibility as people may call
     * PropTypes directly and inspect their output. However, we don't use real
     * Errors anymore. We don't inspect their stack anyway, and creating them
     * is prohibitively expensive if they are created too often, such as what
     * happens in oneOfType() for any type before the one that matched.
     */
    function PropTypeError(message) {
      this.message = message
      this.stack = ''
    }
    // Make `instanceof Error` still work for returned errors.
    PropTypeError.prototype = Error.prototype

    function createChainableTypeChecker(validate) {
      {
        var manualPropTypeCallCache = {}
        var manualPropTypeWarningCount = 0
      }
      function checkType(
        isRequired,
        props,
        propName,
        componentName,
        location,
        propFullName,
        secret
      ) {
        componentName = componentName || ANONYMOUS
        propFullName = propFullName || propName

        if (secret !== ReactPropTypesSecret_1) {
          if (throwOnDirectAccess) {
            // New behavior only for users of `prop-types` package
            var err = new Error(
              'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
                'Use `PropTypes.checkPropTypes()` to call them. ' +
                'Read more at http://fb.me/use-check-prop-types'
            )
            err.name = 'Invariant Violation'
            throw err
          } else if (typeof console !== 'undefined') {
            // Old behavior for people using React.PropTypes
            var cacheKey = componentName + ':' + propName
            if (
              !manualPropTypeCallCache[cacheKey] &&
              // Avoid spamming the console because they are often not actionable except for lib authors
              manualPropTypeWarningCount < 3
            ) {
              printWarning$1(
                'You are manually calling a React.PropTypes validation ' +
                  'function for the `' +
                  propFullName +
                  '` prop on `' +
                  componentName +
                  '`. This is deprecated ' +
                  'and will throw in the standalone `prop-types` package. ' +
                  'You may be seeing this warning due to a third-party PropTypes ' +
                  'library. See https://fb.me/react-warning-dont-call-proptypes ' +
                  'for details.'
              )
              manualPropTypeCallCache[cacheKey] = true
              manualPropTypeWarningCount++
            }
          }
        }
        if (props[propName] == null) {
          if (isRequired) {
            if (props[propName] === null) {
              return new PropTypeError(
                'The ' +
                  location +
                  ' `' +
                  propFullName +
                  '` is marked as required ' +
                  ('in `' + componentName + '`, but its value is `null`.')
              )
            }
            return new PropTypeError(
              'The ' +
                location +
                ' `' +
                propFullName +
                '` is marked as required in ' +
                ('`' + componentName + '`, but its value is `undefined`.')
            )
          }
          return null
        } else {
          return validate(
            props,
            propName,
            componentName,
            location,
            propFullName
          )
        }
      }

      var chainedCheckType = checkType.bind(null, false)
      chainedCheckType.isRequired = checkType.bind(null, true)

      return chainedCheckType
    }

    function createPrimitiveTypeChecker(expectedType) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName,
        secret
      ) {
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== expectedType) {
          // `propValue` being instance of, say, date/regexp, pass the 'object'
          // check, but we can offer a more precise error message here rather than
          // 'of type `object`'.
          var preciseType = getPreciseType(propValue)

          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                preciseType +
                '` supplied to `' +
                componentName +
                '`, expected ') +
              ('`' + expectedType + '`.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createAnyTypeChecker() {
      return createChainableTypeChecker(emptyFunctionThatReturnsNull)
    }

    function createArrayOfTypeChecker(typeChecker) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError(
            'Property `' +
              propFullName +
              '` of component `' +
              componentName +
              '` has invalid PropType notation inside arrayOf.'
          )
        }
        var propValue = props[propName]
        if (!Array.isArray(propValue)) {
          var propType = getPropType(propValue)
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected an array.')
          )
        }
        for (var i = 0; i < propValue.length; i++) {
          var error = typeChecker(
            propValue,
            i,
            componentName,
            location,
            propFullName + '[' + i + ']',
            ReactPropTypesSecret_1
          )
          if (error instanceof Error) {
            return error
          }
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createElementTypeChecker() {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        if (!isValidElement(propValue)) {
          var propType = getPropType(propValue)
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected a single ReactElement.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createElementTypeTypeChecker() {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        if (!reactIs.isValidElementType(propValue)) {
          var propType = getPropType(propValue)
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected a single ReactElement type.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createInstanceTypeChecker(expectedClass) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (!(props[propName] instanceof expectedClass)) {
          var expectedClassName = expectedClass.name || ANONYMOUS
          var actualClassName = getClassName(props[propName])
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                actualClassName +
                '` supplied to `' +
                componentName +
                '`, expected ') +
              ('instance of `' + expectedClassName + '`.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createEnumTypeChecker(expectedValues) {
      if (!Array.isArray(expectedValues)) {
        {
          if (arguments.length > 1) {
            printWarning$1(
              'Invalid arguments supplied to oneOf, expected an array, got ' +
                arguments.length +
                ' arguments. ' +
                'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
            )
          } else {
            printWarning$1(
              'Invalid argument supplied to oneOf, expected an array.'
            )
          }
        }
        return emptyFunctionThatReturnsNull
      }

      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        for (var i = 0; i < expectedValues.length; i++) {
          if (is(propValue, expectedValues[i])) {
            return null
          }
        }

        var valuesString = JSON.stringify(expectedValues, function replacer(
          key,
          value
        ) {
          var type = getPreciseType(value)
          if (type === 'symbol') {
            return String(value)
          }
          return value
        })
        return new PropTypeError(
          'Invalid ' +
            location +
            ' `' +
            propFullName +
            '` of value `' +
            String(propValue) +
            '` ' +
            ('supplied to `' +
              componentName +
              '`, expected one of ' +
              valuesString +
              '.')
        )
      }
      return createChainableTypeChecker(validate)
    }

    function createObjectOfTypeChecker(typeChecker) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (typeof typeChecker !== 'function') {
          return new PropTypeError(
            'Property `' +
              propFullName +
              '` of component `' +
              componentName +
              '` has invalid PropType notation inside objectOf.'
          )
        }
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== 'object') {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type ' +
              ('`' +
                propType +
                '` supplied to `' +
                componentName +
                '`, expected an object.')
          )
        }
        for (var key in propValue) {
          if (has$1(propValue, key)) {
            var error = typeChecker(
              propValue,
              key,
              componentName,
              location,
              propFullName + '.' + key,
              ReactPropTypesSecret_1
            )
            if (error instanceof Error) {
              return error
            }
          }
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createUnionTypeChecker(arrayOfTypeCheckers) {
      if (!Array.isArray(arrayOfTypeCheckers)) {
        printWarning$1(
          'Invalid argument supplied to oneOfType, expected an instance of array.'
        )
        return emptyFunctionThatReturnsNull
      }

      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
        var checker = arrayOfTypeCheckers[i]
        if (typeof checker !== 'function') {
          printWarning$1(
            'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
              'received ' +
              getPostfixForTypeWarning(checker) +
              ' at index ' +
              i +
              '.'
          )
          return emptyFunctionThatReturnsNull
        }
      }

      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
          var checker = arrayOfTypeCheckers[i]
          if (
            checker(
              props,
              propName,
              componentName,
              location,
              propFullName,
              ReactPropTypesSecret_1
            ) == null
          ) {
            return null
          }
        }

        return new PropTypeError(
          'Invalid ' +
            location +
            ' `' +
            propFullName +
            '` supplied to ' +
            ('`' + componentName + '`.')
        )
      }
      return createChainableTypeChecker(validate)
    }

    function createNodeChecker() {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        if (!isNode(props[propName])) {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` supplied to ' +
              ('`' + componentName + '`, expected a ReactNode.')
          )
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createShapeTypeChecker(shapeTypes) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== 'object') {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type `' +
              propType +
              '` ' +
              ('supplied to `' + componentName + '`, expected `object`.')
          )
        }
        for (var key in shapeTypes) {
          var checker = shapeTypes[key]
          if (!checker) {
            continue
          }
          var error = checker(
            propValue,
            key,
            componentName,
            location,
            propFullName + '.' + key,
            ReactPropTypesSecret_1
          )
          if (error) {
            return error
          }
        }
        return null
      }
      return createChainableTypeChecker(validate)
    }

    function createStrictShapeTypeChecker(shapeTypes) {
      function validate(
        props,
        propName,
        componentName,
        location,
        propFullName
      ) {
        var propValue = props[propName]
        var propType = getPropType(propValue)
        if (propType !== 'object') {
          return new PropTypeError(
            'Invalid ' +
              location +
              ' `' +
              propFullName +
              '` of type `' +
              propType +
              '` ' +
              ('supplied to `' + componentName + '`, expected `object`.')
          )
        }
        // We need to check all keys in case some are required but missing from
        // props.
        var allKeys = objectAssign({}, props[propName], shapeTypes)
        for (var key in allKeys) {
          var checker = shapeTypes[key]
          if (!checker) {
            return new PropTypeError(
              'Invalid ' +
                location +
                ' `' +
                propFullName +
                '` key `' +
                key +
                '` supplied to `' +
                componentName +
                '`.' +
                '\nBad object: ' +
                JSON.stringify(props[propName], null, '  ') +
                '\nValid keys: ' +
                JSON.stringify(Object.keys(shapeTypes), null, '  ')
            )
          }
          var error = checker(
            propValue,
            key,
            componentName,
            location,
            propFullName + '.' + key,
            ReactPropTypesSecret_1
          )
          if (error) {
            return error
          }
        }
        return null
      }

      return createChainableTypeChecker(validate)
    }

    function isNode(propValue) {
      switch (typeof propValue) {
        case 'number':
        case 'string':
        case 'undefined':
          return true
        case 'boolean':
          return !propValue
        case 'object':
          if (Array.isArray(propValue)) {
            return propValue.every(isNode)
          }
          if (propValue === null || isValidElement(propValue)) {
            return true
          }

          var iteratorFn = getIteratorFn(propValue)
          if (iteratorFn) {
            var iterator = iteratorFn.call(propValue)
            var step
            if (iteratorFn !== propValue.entries) {
              while (!(step = iterator.next()).done) {
                if (!isNode(step.value)) {
                  return false
                }
              }
            } else {
              // Iterator will provide entry [k,v] tuples rather than values.
              while (!(step = iterator.next()).done) {
                var entry = step.value
                if (entry) {
                  if (!isNode(entry[1])) {
                    return false
                  }
                }
              }
            }
          } else {
            return false
          }

          return true
        default:
          return false
      }
    }

    function isSymbol(propType, propValue) {
      // Native Symbol.
      if (propType === 'symbol') {
        return true
      }

      // falsy value can't be a Symbol
      if (!propValue) {
        return false
      }

      // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
      if (propValue['@@toStringTag'] === 'Symbol') {
        return true
      }

      // Fallback for non-spec compliant Symbols which are polyfilled.
      if (typeof Symbol === 'function' && propValue instanceof Symbol) {
        return true
      }

      return false
    }

    // Equivalent of `typeof` but with special handling for array and regexp.
    function getPropType(propValue) {
      var propType = typeof propValue
      if (Array.isArray(propValue)) {
        return 'array'
      }
      if (propValue instanceof RegExp) {
        // Old webkits (at least until Android 4.0) return 'function' rather than
        // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
        // passes PropTypes.object.
        return 'object'
      }
      if (isSymbol(propType, propValue)) {
        return 'symbol'
      }
      return propType
    }

    // This handles more types than `getPropType`. Only used for error messages.
    // See `createPrimitiveTypeChecker`.
    function getPreciseType(propValue) {
      if (typeof propValue === 'undefined' || propValue === null) {
        return '' + propValue
      }
      var propType = getPropType(propValue)
      if (propType === 'object') {
        if (propValue instanceof Date) {
          return 'date'
        } else if (propValue instanceof RegExp) {
          return 'regexp'
        }
      }
      return propType
    }

    // Returns a string that is postfixed to a warning about an invalid type.
    // For example, "undefined" or "of type array"
    function getPostfixForTypeWarning(value) {
      var type = getPreciseType(value)
      switch (type) {
        case 'array':
        case 'object':
          return 'an ' + type
        case 'boolean':
        case 'date':
        case 'regexp':
          return 'a ' + type
        default:
          return type
      }
    }

    // Returns class name of the object, if any.
    function getClassName(propValue) {
      if (!propValue.constructor || !propValue.constructor.name) {
        return ANONYMOUS
      }
      return propValue.constructor.name
    }

    ReactPropTypes.checkPropTypes = checkPropTypes_1
    ReactPropTypes.resetWarningCache = checkPropTypes_1.resetWarningCache
    ReactPropTypes.PropTypes = ReactPropTypes

    return ReactPropTypes
  }

  var propTypes = createCommonjsModule(function(module) {
    /**
     * Copyright (c) 2013-present, Facebook, Inc.
     *
     * This source code is licensed under the MIT license found in the
     * LICENSE file in the root directory of this source tree.
     */

    {
      var ReactIs = reactIs

      // By explicitly using `prop-types` you are opting into new development behavior.
      // http://fb.me/prop-types-in-prod
      var throwOnDirectAccess = true
      module.exports = factoryWithTypeCheckers(
        ReactIs.isElement,
        throwOnDirectAccess
      )
    }
  })

  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var invariant = function(condition, format, a, b, c, d, e, f) {
    {
      if (format === undefined) {
        throw new Error('invariant requires an error message argument')
      }
    }

    if (!condition) {
      var error
      if (format === undefined) {
        error = new Error(
          'Minified exception occurred; use the non-minified dev environment ' +
            'for the full error message and additional helpful warnings.'
        )
      } else {
        var args = [a, b, c, d, e, f]
        var argIndex = 0
        error = new Error(
          format.replace(/%s/g, function() {
            return args[argIndex++]
          })
        )
        error.name = 'Invariant Violation'
      }

      error.framesToPop = 1 // we don't care about invariant's own frame
      throw error
    }
  }

  var invariant_1 = invariant

  var noop = function noop() {}

  function readOnlyPropType(handler, name) {
    return function(props, propName) {
      if (props[propName] !== undefined) {
        if (!props[handler]) {
          return new Error(
            'You have provided a `' +
              propName +
              '` prop to `' +
              name +
              '` ' +
              ('without an `' +
                handler +
                '` handler prop. This will render a read-only field. ') +
              ('If the field should be mutable use `' +
                defaultKey(propName) +
                '`. ') +
              ('Otherwise, set `' + handler + '`.')
          )
        }
      }
    }
  }

  function uncontrolledPropTypes(controlledValues, displayName) {
    var propTypes = {}
    Object.keys(controlledValues).forEach(function(prop) {
      // add default propTypes for folks that use runtime checks
      propTypes[defaultKey(prop)] = noop

      {
        var handler = controlledValues[prop]
        !(typeof handler === 'string' && handler.trim().length)
          ? invariant_1(
              false,
              'Uncontrollable - [%s]: the prop `%s` needs a valid handler key name in order to make it uncontrollable',
              displayName,
              prop
            )
          : void 0
        propTypes[prop] = readOnlyPropType(handler, displayName)
      }
    })
    return propTypes
  }
  function isProp(props, prop) {
    return props[prop] !== undefined
  }
  function defaultKey(key) {
    return 'default' + key.charAt(0).toUpperCase() + key.substr(1)
  }
  /**
   * Copyright (c) 2013-present, Facebook, Inc.
   * All rights reserved.
   *
   * This source code is licensed under the BSD-style license found in the
   * LICENSE file in the root directory of this source tree. An additional grant
   * of patent rights can be found in the PATENTS file in the same directory.
   */

  function canAcceptRef(component) {
    return (
      !!component &&
      (typeof component !== 'function' ||
        (component.prototype && component.prototype.isReactComponent))
    )
  }

  function uncontrollable(Component, controlledValues, methods) {
    if (methods === void 0) {
      methods = []
    }

    var displayName = Component.displayName || Component.name || 'Component'
    var canAcceptRef$1 = canAcceptRef(Component)
    var controlledProps = Object.keys(controlledValues)
    var PROPS_TO_OMIT = controlledProps.map(defaultKey)
    !(canAcceptRef$1 || !methods.length)
      ? invariant_1(
          false,
          '[uncontrollable] stateless function components cannot pass through methods ' +
            'because they have no associated instances. Check component: ' +
            displayName +
            ', ' +
            'attempting to pass through methods: ' +
            methods.join(', ')
        )
      : void 0

    var UncontrolledComponent =
      /*#__PURE__*/
      (function(_React$Component) {
        _inheritsLoose(UncontrolledComponent, _React$Component)

        function UncontrolledComponent() {
          var _this

          for (
            var _len = arguments.length, args = new Array(_len), _key = 0;
            _key < _len;
            _key++
          ) {
            args[_key] = arguments[_key]
          }

          _this =
            _React$Component.call.apply(
              _React$Component,
              [this].concat(args)
            ) || this
          _this.handlers = Object.create(null)
          controlledProps.forEach(function(propName) {
            var handlerName = controlledValues[propName]

            var handleChange = function handleChange(value) {
              if (_this.props[handlerName]) {
                var _this$props

                _this._notifying = true

                for (
                  var _len2 = arguments.length,
                    args = new Array(_len2 > 1 ? _len2 - 1 : 0),
                    _key2 = 1;
                  _key2 < _len2;
                  _key2++
                ) {
                  args[_key2 - 1] = arguments[_key2]
                }

                ;(_this$props = _this.props)[handlerName].apply(
                  _this$props,
                  [value].concat(args)
                )

                _this._notifying = false
              }

              _this._values[propName] = value
              if (!_this.unmounted) _this.forceUpdate()
            }

            _this.handlers[handlerName] = handleChange
          })
          if (methods.length)
            _this.attachRef = function(ref) {
              _this.inner = ref
            }
          return _this
        }

        var _proto = UncontrolledComponent.prototype

        _proto.shouldComponentUpdate = function shouldComponentUpdate() {
          //let the forceUpdate trigger the update
          return !this._notifying
        }

        _proto.componentWillMount = function componentWillMount() {
          var _this2 = this

          var props = this.props
          this._values = Object.create(null)
          controlledProps.forEach(function(key) {
            _this2._values[key] = props[defaultKey(key)]
          })
        }

        _proto.componentWillReceiveProps = function componentWillReceiveProps(
          nextProps
        ) {
          var _this3 = this

          var props = this.props
          controlledProps.forEach(function(key) {
            /**
             * If a prop switches from controlled to Uncontrolled
             * reset its value to the defaultValue
             */
            if (!isProp(nextProps, key) && isProp(props, key)) {
              _this3._values[key] = nextProps[defaultKey(key)]
            }
          })
        }

        _proto.componentWillUnmount = function componentWillUnmount() {
          this.unmounted = true
        }

        _proto.render = function render() {
          var _this4 = this

          var _this$props2 = this.props,
            innerRef = _this$props2.innerRef,
            props = _objectWithoutPropertiesLoose(_this$props2, ['innerRef'])

          PROPS_TO_OMIT.forEach(function(prop) {
            delete props[prop]
          })
          var newProps = {}
          controlledProps.forEach(function(propName) {
            var propValue = _this4.props[propName]
            newProps[propName] =
              propValue !== undefined ? propValue : _this4._values[propName]
          })
          return React__default.createElement(
            Component,
            _extends({}, props, newProps, this.handlers, {
              ref: innerRef || this.attachRef,
            })
          )
        }

        return UncontrolledComponent
      })(React__default.Component)

    UncontrolledComponent.displayName = 'Uncontrolled(' + displayName + ')'
    UncontrolledComponent.propTypes = _extends(
      {
        innerRef: function innerRef() {},
      },
      uncontrolledPropTypes(controlledValues, displayName)
    )
    methods.forEach(function(method) {
      UncontrolledComponent.prototype[method] = function $proxiedMethod() {
        var _this$inner

        return (_this$inner = this.inner)[method].apply(_this$inner, arguments)
      }
    })
    var WrappedComponent = UncontrolledComponent

    if (React__default.forwardRef) {
      WrappedComponent = React__default.forwardRef(function(props, ref) {
        return React__default.createElement(
          UncontrolledComponent,
          _extends({}, props, {
            innerRef: ref,
          })
        )
      })
      WrappedComponent.propTypes = UncontrolledComponent.propTypes
    }

    WrappedComponent.ControlledComponent = Component
    /**
     * useful when wrapping a Component and you want to control
     * everything
     */

    WrappedComponent.deferControlTo = function(
      newComponent,
      additions,
      nextMethods
    ) {
      if (additions === void 0) {
        additions = {}
      }

      return uncontrollable(
        newComponent,
        _extends({}, controlledValues, additions),
        nextMethods
      )
    }

    return WrappedComponent
  }

  function toVal(mix) {
    var k,
      y,
      str = ''
    if (mix) {
      if (typeof mix === 'object') {
        if (!!mix.push) {
          for (k = 0; k < mix.length; k++) {
            if (mix[k] && (y = toVal(mix[k]))) {
              str && (str += ' ')
              str += y
            }
          }
        } else {
          for (k in mix) {
            if (mix[k] && (y = toVal(k))) {
              str && (str += ' ')
              str += y
            }
          }
        }
      } else if (typeof mix !== 'boolean' && !mix.call) {
        str && (str += ' ')
        str += mix
      }
    }
    return str
  }

  function clsx() {
    var i = 0,
      x,
      str = ''
    while (i < arguments.length) {
      if ((x = toVal(arguments[i++]))) {
        str && (str += ' ')
        str += x
      }
    }
    return str
  }

  var navigate = {
    PREVIOUS: 'PREV',
    NEXT: 'NEXT',
    TODAY: 'TODAY',
    DATE: 'DATE',
  }
  var views = {
    DAY: 'day',
    WEEK: 'week',
    MONTH: 'month',
    WORK_WEEK: 'work_week',
    AGENDA: 'agenda',
  }

  var viewNames = Object.keys(views).map(function(k) {
    return views[k]
  })
  var accessor = propTypes.oneOfType([propTypes.string, propTypes.func])
  var dateFormat = propTypes.any
  var dateRangeFormat = propTypes.func
  /**
   * accepts either an array of builtin view names:
   *
   * ```
   * views={['month', 'day', 'agenda']}
   * ```
   *
   * or an object hash of the view name and the component (or boolean for builtin)
   *
   * ```
   * views={{
   *   month: true,
   *   week: false,
   *   workweek: WorkWeekViewComponent,
   * }}
   * ```
   */

  var views$1 = propTypes.oneOfType([
    propTypes.arrayOf(propTypes.oneOf(viewNames)),
    propTypes.objectOf(function(prop, key) {
      var isBuiltinView =
        viewNames.indexOf(key) !== -1 && typeof prop[key] === 'boolean'

      if (isBuiltinView) {
        return null
      } else {
        for (
          var _len = arguments.length,
            args = new Array(_len > 2 ? _len - 2 : 0),
            _key = 2;
          _key < _len;
          _key++
        ) {
          args[_key - 2] = arguments[_key]
        }

        return propTypes.elementType.apply(propTypes, [prop, key].concat(args))
      }
    }),
  ])

  /**
   * Copyright (c) 2014-present, Facebook, Inc.
   *
   * This source code is licensed under the MIT license found in the
   * LICENSE file in the root directory of this source tree.
   */

  var warning = function() {}

  {
    var printWarning$2 = function printWarning(format, args) {
      var len = arguments.length
      args = new Array(len > 1 ? len - 1 : 0)
      for (var key = 1; key < len; key++) {
        args[key - 1] = arguments[key]
      }
      var argIndex = 0
      var message =
        'Warning: ' +
        format.replace(/%s/g, function() {
          return args[argIndex++]
        })
      if (typeof console !== 'undefined') {
        console.error(message)
      }
      try {
        // --- Welcome to debugging React ---
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message)
      } catch (x) {}
    }

    warning = function(condition, format, args) {
      var len = arguments.length
      args = new Array(len > 2 ? len - 2 : 0)
      for (var key = 2; key < len; key++) {
        args[key - 2] = arguments[key]
      }
      if (format === undefined) {
        throw new Error(
          '`warning(condition, format, ...args)` requires a warning ' +
            'message argument'
        )
      }
      if (!condition) {
        printWarning$2.apply(null, [format].concat(args))
      }
    }
  }

  var warning_1 = warning

  function notify(handler, args) {
    handler && handler.apply(null, [].concat(args))
  }

  var localePropType = propTypes.oneOfType([propTypes.string, propTypes.func])

  function _format(localizer, formatter, value, format, culture) {
    var result =
      typeof format === 'function'
        ? format(value, culture, localizer)
        : formatter.call(localizer, value, format, culture)
    !(result == null || typeof result === 'string')
      ? invariant_1(
          false,
          '`localizer format(..)` must return a string, null, or undefined'
        )
      : void 0
    return result
  }

  var DateLocalizer = function DateLocalizer(spec) {
    var _this = this

    !(typeof spec.format === 'function')
      ? invariant_1(false, 'date localizer `format(..)` must be a function')
      : void 0
    !(typeof spec.firstOfWeek === 'function')
      ? invariant_1(
          false,
          'date localizer `firstOfWeek(..)` must be a function'
        )
      : void 0
    this.propType = spec.propType || localePropType
    this.startOfWeek = spec.firstOfWeek
    this.formats = spec.formats

    this.format = function() {
      for (
        var _len = arguments.length, args = new Array(_len), _key = 0;
        _key < _len;
        _key++
      ) {
        args[_key] = arguments[_key]
      }

      return _format.apply(void 0, [_this, spec.format].concat(args))
    }
  }
  function mergeWithDefaults(localizer, culture, formatOverrides, messages) {
    var formats = _extends({}, localizer.formats, {}, formatOverrides)

    return _extends({}, localizer, {
      messages: messages,
      startOfWeek: function startOfWeek() {
        return localizer.startOfWeek(culture)
      },
      format: function format(value, _format2) {
        return localizer.format(value, formats[_format2] || _format2, culture)
      },
    })
  }

  var defaultMessages = {
    date: 'Date',
    time: 'Time',
    event: 'Event',
    allDay: 'All Day',
    week: 'Week',
    work_week: 'Work Week',
    day: 'Day',
    month: 'Month',
    previous: 'Back',
    next: 'Next',
    yesterday: 'Yesterday',
    tomorrow: 'Tomorrow',
    today: 'Today',
    agenda: 'Agenda',
    noEventsInRange: 'There are no events in this range.',
    showMore: function showMore(total) {
      return '+' + total + ' more'
    },
  }
  function messages(msgs) {
    return _extends({}, defaultMessages, {}, msgs)
  }

  function _assertThisInitialized(self) {
    if (self === void 0) {
      throw new ReferenceError(
        "this hasn't been initialised - super() hasn't been called"
      )
    }

    return self
  }

  var MILI = 'milliseconds',
    SECONDS = 'seconds',
    MINUTES = 'minutes',
    HOURS = 'hours',
    DAY = 'day',
    WEEK = 'week',
    MONTH = 'month',
    YEAR = 'year',
    DECADE = 'decade',
    CENTURY = 'century'

  function add(d, num, unit) {
    d = new Date(d)

    switch (unit) {
      case MILI:
        return milliseconds(d, milliseconds(d) + num)
      case SECONDS:
        return seconds(d, seconds(d) + num)
      case MINUTES:
        return minutes(d, minutes(d) + num)
      case HOURS:
        return hours(d, hours(d) + num)
      case YEAR:
        return year(d, year(d) + num)
      case DAY:
        return date(d, date(d) + num)
      case WEEK:
        return date(d, date(d) + 7 * num)
      case MONTH:
        return monthMath(d, num)
      case DECADE:
        return year(d, year(d) + num * 10)
      case CENTURY:
        return year(d, year(d) + num * 100)
    }

    throw new TypeError('Invalid units: "' + unit + '"')
  }

  function subtract(d, num, unit) {
    return add(d, -num, unit)
  }

  function startOf(d, unit, firstOfWeek) {
    d = new Date(d)

    switch (unit) {
      case CENTURY:
      case DECADE:
      case YEAR:
        d = month(d, 0)
      case MONTH:
        d = date(d, 1)
      case WEEK:
      case DAY:
        d = hours(d, 0)
      case HOURS:
        d = minutes(d, 0)
      case MINUTES:
        d = seconds(d, 0)
      case SECONDS:
        d = milliseconds(d, 0)
    }

    if (unit === DECADE) d = subtract(d, year(d) % 10, 'year')

    if (unit === CENTURY) d = subtract(d, year(d) % 100, 'year')

    if (unit === WEEK) d = weekday(d, 0, firstOfWeek)

    return d
  }

  function endOf(d, unit, firstOfWeek) {
    d = new Date(d)
    d = startOf(d, unit, firstOfWeek)
    d = add(d, 1, unit)
    d = subtract(d, 1, MILI)
    return d
  }

  var eq = createComparer(function(a, b) {
    return a === b
  })
  var gt = createComparer(function(a, b) {
    return a > b
  })
  var gte = createComparer(function(a, b) {
    return a >= b
  })
  var lt = createComparer(function(a, b) {
    return a < b
  })
  var lte = createComparer(function(a, b) {
    return a <= b
  })

  function min() {
    return new Date(Math.min.apply(Math, arguments))
  }

  function max() {
    return new Date(Math.max.apply(Math, arguments))
  }

  function inRange(day, min, max, unit) {
    unit = unit || 'day'

    return (!min || gte(day, min, unit)) && (!max || lte(day, max, unit))
  }

  var milliseconds = createAccessor('Milliseconds')
  var seconds = createAccessor('Seconds')
  var minutes = createAccessor('Minutes')
  var hours = createAccessor('Hours')
  var day = createAccessor('Day')
  var date = createAccessor('Date')
  var month = createAccessor('Month')
  var year = createAccessor('FullYear')

  function weekday(d, val, firstDay) {
    var w = (day(d) + 7 - (firstDay || 0)) % 7

    return val === undefined ? w : add(d, val - w, DAY)
  }

  function monthMath(d, val) {
    var current = month(d),
      newMonth = current + val

    d = month(d, newMonth)

    while (newMonth < 0) newMonth = 12 + newMonth

    //month rollover
    if (month(d) !== newMonth % 12) d = date(d, 0) //move to last of month

    return d
  }

  function createAccessor(method) {
    var hourLength = (function(method) {
      switch (method) {
        case 'Milliseconds':
          return 3600000
        case 'Seconds':
          return 3600
        case 'Minutes':
          return 60
        case 'Hours':
          return 1
        default:
          return null
      }
    })(method)

    return function(d, val) {
      if (val === undefined) return d['get' + method]()

      var dateOut = new Date(d)
      dateOut['set' + method](val)

      if (
        hourLength &&
        dateOut['get' + method]() != val &&
        (method === 'Hours' ||
          (val >= hourLength &&
            dateOut.getHours() - d.getHours() < Math.floor(val / hourLength)))
      ) {
        //Skip DST hour, if it occurs
        dateOut['set' + method](val + hourLength)
      }

      return dateOut
    }
  }

  function createComparer(operator) {
    return function(a, b, unit) {
      return operator(+startOf(a, unit), +startOf(b, unit))
    }
  }

  /* eslint no-fallthrough: off */
  var MILLI = {
    seconds: 1000,
    minutes: 1000 * 60,
    hours: 1000 * 60 * 60,
    day: 1000 * 60 * 60 * 24,
  }
  function firstVisibleDay(date, localizer) {
    var firstOfMonth = startOf(date, 'month')
    return startOf(firstOfMonth, 'week', localizer.startOfWeek())
  }
  function lastVisibleDay(date, localizer) {
    var endOfMonth = endOf(date, 'month')
    return endOf(endOfMonth, 'week', localizer.startOfWeek())
  }
  function visibleDays(date, localizer) {
    var current = firstVisibleDay(date, localizer),
      last = lastVisibleDay(date, localizer),
      days = []

    while (lte(current, last, 'day')) {
      days.push(current)
      current = add(current, 1, 'day')
    }

    return days
  }
  function ceil(date, unit) {
    var floor = startOf(date, unit)
    return eq(floor, date) ? floor : add(floor, 1, unit)
  }
  function range(start, end, unit) {
    if (unit === void 0) {
      unit = 'day'
    }

    var current = start,
      days = []

    while (lte(current, end, unit)) {
      days.push(current)
      current = add(current, 1, unit)
    }

    return days
  }
  function merge(date, time) {
    if (time == null && date == null) return null
    if (time == null) time = new Date()
    if (date == null) date = new Date()
    date = startOf(date, 'day')
    date = hours(date, hours(time))
    date = minutes(date, minutes(time))
    date = seconds(date, seconds(time))
    return milliseconds(date, milliseconds(time))
  }
  function isJustDate(date) {
    return (
      hours(date) === 0 &&
      minutes(date) === 0 &&
      seconds(date) === 0 &&
      milliseconds(date) === 0
    )
  }
  function diff(dateA, dateB, unit) {
    if (!unit || unit === 'milliseconds') return Math.abs(+dateA - +dateB) // the .round() handles an edge case
    // with DST where the total won't be exact
    // since one day in the range may be shorter/longer by an hour

    return Math.round(
      Math.abs(
        +startOf(dateA, unit) / MILLI[unit] -
          +startOf(dateB, unit) / MILLI[unit]
      )
    )
  }

  /**
   * The base implementation of `_.slice` without an iteratee call guard.
   *
   * @private
   * @param {Array} array The array to slice.
   * @param {number} [start=0] The start position.
   * @param {number} [end=array.length] The end position.
   * @returns {Array} Returns the slice of `array`.
   */
  function baseSlice(array, start, end) {
    var index = -1,
      length = array.length

    if (start < 0) {
      start = -start > length ? 0 : length + start
    }
    end = end > length ? length : end
    if (end < 0) {
      end += length
    }
    length = start > end ? 0 : (end - start) >>> 0
    start >>>= 0

    var result = Array(length)
    while (++index < length) {
      result[index] = array[index + start]
    }
    return result
  }

  /**
   * Performs a
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * comparison between two values to determine if they are equivalent.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
   * @example
   *
   * var object = { 'a': 1 };
   * var other = { 'a': 1 };
   *
   * _.eq(object, object);
   * // => true
   *
   * _.eq(object, other);
   * // => false
   *
   * _.eq('a', 'a');
   * // => true
   *
   * _.eq('a', Object('a'));
   * // => false
   *
   * _.eq(NaN, NaN);
   * // => true
   */
  function eq$1(value, other) {
    return value === other || (value !== value && other !== other)
  }

  /** Detect free variable `global` from Node.js. */
  var freeGlobal =
    typeof global == 'object' && global && global.Object === Object && global

  /** Detect free variable `self`. */
  var freeSelf =
    typeof self == 'object' && self && self.Object === Object && self

  /** Used as a reference to the global object. */
  var root = freeGlobal || freeSelf || Function('return this')()

  /** Built-in value references. */
  var Symbol$1 = root.Symbol

  /** Used for built-in method references. */
  var objectProto = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$1 = objectProto.hasOwnProperty

  /**
   * Used to resolve the
   * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
   * of values.
   */
  var nativeObjectToString = objectProto.toString

  /** Built-in value references. */
  var symToStringTag = Symbol$1 ? Symbol$1.toStringTag : undefined

  /**
   * A specialized version of `baseGetTag` which ignores `Symbol.toStringTag` values.
   *
   * @private
   * @param {*} value The value to query.
   * @returns {string} Returns the raw `toStringTag`.
   */
  function getRawTag(value) {
    var isOwn = hasOwnProperty$1.call(value, symToStringTag),
      tag = value[symToStringTag]

    try {
      value[symToStringTag] = undefined
      var unmasked = true
    } catch (e) {}

    var result = nativeObjectToString.call(value)
    if (unmasked) {
      if (isOwn) {
        value[symToStringTag] = tag
      } else {
        delete value[symToStringTag]
      }
    }
    return result
  }

  /** Used for built-in method references. */
  var objectProto$1 = Object.prototype

  /**
   * Used to resolve the
   * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
   * of values.
   */
  var nativeObjectToString$1 = objectProto$1.toString

  /**
   * Converts `value` to a string using `Object.prototype.toString`.
   *
   * @private
   * @param {*} value The value to convert.
   * @returns {string} Returns the converted string.
   */
  function objectToString(value) {
    return nativeObjectToString$1.call(value)
  }

  /** `Object#toString` result references. */
  var nullTag = '[object Null]',
    undefinedTag = '[object Undefined]'

  /** Built-in value references. */
  var symToStringTag$1 = Symbol$1 ? Symbol$1.toStringTag : undefined

  /**
   * The base implementation of `getTag` without fallbacks for buggy environments.
   *
   * @private
   * @param {*} value The value to query.
   * @returns {string} Returns the `toStringTag`.
   */
  function baseGetTag(value) {
    if (value == null) {
      return value === undefined ? undefinedTag : nullTag
    }
    return symToStringTag$1 && symToStringTag$1 in Object(value)
      ? getRawTag(value)
      : objectToString(value)
  }

  /**
   * Checks if `value` is the
   * [language type](http://www.ecma-international.org/ecma-262/7.0/#sec-ecmascript-language-types)
   * of `Object`. (e.g. arrays, functions, objects, regexes, `new Number(0)`, and `new String('')`)
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an object, else `false`.
   * @example
   *
   * _.isObject({});
   * // => true
   *
   * _.isObject([1, 2, 3]);
   * // => true
   *
   * _.isObject(_.noop);
   * // => true
   *
   * _.isObject(null);
   * // => false
   */
  function isObject(value) {
    var type = typeof value
    return value != null && (type == 'object' || type == 'function')
  }

  /** `Object#toString` result references. */
  var asyncTag = '[object AsyncFunction]',
    funcTag = '[object Function]',
    genTag = '[object GeneratorFunction]',
    proxyTag = '[object Proxy]'

  /**
   * Checks if `value` is classified as a `Function` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a function, else `false`.
   * @example
   *
   * _.isFunction(_);
   * // => true
   *
   * _.isFunction(/abc/);
   * // => false
   */
  function isFunction(value) {
    if (!isObject(value)) {
      return false
    }
    // The use of `Object#toString` avoids issues with the `typeof` operator
    // in Safari 9 which returns 'object' for typed arrays and other constructors.
    var tag = baseGetTag(value)
    return tag == funcTag || tag == genTag || tag == asyncTag || tag == proxyTag
  }

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER = 9007199254740991

  /**
   * Checks if `value` is a valid array-like length.
   *
   * **Note:** This method is loosely based on
   * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a valid length, else `false`.
   * @example
   *
   * _.isLength(3);
   * // => true
   *
   * _.isLength(Number.MIN_VALUE);
   * // => false
   *
   * _.isLength(Infinity);
   * // => false
   *
   * _.isLength('3');
   * // => false
   */
  function isLength(value) {
    return (
      typeof value == 'number' &&
      value > -1 &&
      value % 1 == 0 &&
      value <= MAX_SAFE_INTEGER
    )
  }

  /**
   * Checks if `value` is array-like. A value is considered array-like if it's
   * not a function and has a `value.length` that's an integer greater than or
   * equal to `0` and less than or equal to `Number.MAX_SAFE_INTEGER`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is array-like, else `false`.
   * @example
   *
   * _.isArrayLike([1, 2, 3]);
   * // => true
   *
   * _.isArrayLike(document.body.children);
   * // => true
   *
   * _.isArrayLike('abc');
   * // => true
   *
   * _.isArrayLike(_.noop);
   * // => false
   */
  function isArrayLike(value) {
    return value != null && isLength(value.length) && !isFunction(value)
  }

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER$1 = 9007199254740991

  /** Used to detect unsigned integer values. */
  var reIsUint = /^(?:0|[1-9]\d*)$/

  /**
   * Checks if `value` is a valid array-like index.
   *
   * @private
   * @param {*} value The value to check.
   * @param {number} [length=MAX_SAFE_INTEGER] The upper bounds of a valid index.
   * @returns {boolean} Returns `true` if `value` is a valid index, else `false`.
   */
  function isIndex(value, length) {
    var type = typeof value
    length = length == null ? MAX_SAFE_INTEGER$1 : length

    return (
      !!length &&
      (type == 'number' || (type != 'symbol' && reIsUint.test(value))) &&
      (value > -1 && value % 1 == 0 && value < length)
    )
  }

  /**
   * Checks if the given arguments are from an iteratee call.
   *
   * @private
   * @param {*} value The potential iteratee value argument.
   * @param {*} index The potential iteratee index or key argument.
   * @param {*} object The potential iteratee object argument.
   * @returns {boolean} Returns `true` if the arguments are from an iteratee call,
   *  else `false`.
   */
  function isIterateeCall(value, index, object) {
    if (!isObject(object)) {
      return false
    }
    var type = typeof index
    if (
      type == 'number'
        ? isArrayLike(object) && isIndex(index, object.length)
        : type == 'string' && index in object
    ) {
      return eq$1(object[index], value)
    }
    return false
  }

  /**
   * Checks if `value` is object-like. A value is object-like if it's not `null`
   * and has a `typeof` result of "object".
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is object-like, else `false`.
   * @example
   *
   * _.isObjectLike({});
   * // => true
   *
   * _.isObjectLike([1, 2, 3]);
   * // => true
   *
   * _.isObjectLike(_.noop);
   * // => false
   *
   * _.isObjectLike(null);
   * // => false
   */
  function isObjectLike(value) {
    return value != null && typeof value == 'object'
  }

  /** `Object#toString` result references. */
  var symbolTag = '[object Symbol]'

  /**
   * Checks if `value` is classified as a `Symbol` primitive or object.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a symbol, else `false`.
   * @example
   *
   * _.isSymbol(Symbol.iterator);
   * // => true
   *
   * _.isSymbol('abc');
   * // => false
   */
  function isSymbol(value) {
    return (
      typeof value == 'symbol' ||
      (isObjectLike(value) && baseGetTag(value) == symbolTag)
    )
  }

  /** Used as references for various `Number` constants. */
  var NAN = 0 / 0

  /** Used to match leading and trailing whitespace. */
  var reTrim = /^\s+|\s+$/g

  /** Used to detect bad signed hexadecimal string values. */
  var reIsBadHex = /^[-+]0x[0-9a-f]+$/i

  /** Used to detect binary string values. */
  var reIsBinary = /^0b[01]+$/i

  /** Used to detect octal string values. */
  var reIsOctal = /^0o[0-7]+$/i

  /** Built-in method references without a dependency on `root`. */
  var freeParseInt = parseInt

  /**
   * Converts `value` to a number.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to process.
   * @returns {number} Returns the number.
   * @example
   *
   * _.toNumber(3.2);
   * // => 3.2
   *
   * _.toNumber(Number.MIN_VALUE);
   * // => 5e-324
   *
   * _.toNumber(Infinity);
   * // => Infinity
   *
   * _.toNumber('3.2');
   * // => 3.2
   */
  function toNumber(value) {
    if (typeof value == 'number') {
      return value
    }
    if (isSymbol(value)) {
      return NAN
    }
    if (isObject(value)) {
      var other = typeof value.valueOf == 'function' ? value.valueOf() : value
      value = isObject(other) ? other + '' : other
    }
    if (typeof value != 'string') {
      return value === 0 ? value : +value
    }
    value = value.replace(reTrim, '')
    var isBinary = reIsBinary.test(value)
    return isBinary || reIsOctal.test(value)
      ? freeParseInt(value.slice(2), isBinary ? 2 : 8)
      : reIsBadHex.test(value)
      ? NAN
      : +value
  }

  /** Used as references for various `Number` constants. */
  var INFINITY = 1 / 0,
    MAX_INTEGER = 1.7976931348623157e308

  /**
   * Converts `value` to a finite number.
   *
   * @static
   * @memberOf _
   * @since 4.12.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {number} Returns the converted number.
   * @example
   *
   * _.toFinite(3.2);
   * // => 3.2
   *
   * _.toFinite(Number.MIN_VALUE);
   * // => 5e-324
   *
   * _.toFinite(Infinity);
   * // => 1.7976931348623157e+308
   *
   * _.toFinite('3.2');
   * // => 3.2
   */
  function toFinite(value) {
    if (!value) {
      return value === 0 ? value : 0
    }
    value = toNumber(value)
    if (value === INFINITY || value === -INFINITY) {
      var sign = value < 0 ? -1 : 1
      return sign * MAX_INTEGER
    }
    return value === value ? value : 0
  }

  /**
   * Converts `value` to an integer.
   *
   * **Note:** This method is loosely based on
   * [`ToInteger`](http://www.ecma-international.org/ecma-262/7.0/#sec-tointeger).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {number} Returns the converted integer.
   * @example
   *
   * _.toInteger(3.2);
   * // => 3
   *
   * _.toInteger(Number.MIN_VALUE);
   * // => 0
   *
   * _.toInteger(Infinity);
   * // => 1.7976931348623157e+308
   *
   * _.toInteger('3.2');
   * // => 3
   */
  function toInteger(value) {
    var result = toFinite(value),
      remainder = result % 1

    return result === result ? (remainder ? result - remainder : result) : 0
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeCeil = Math.ceil,
    nativeMax = Math.max

  /**
   * Creates an array of elements split into groups the length of `size`.
   * If `array` can't be split evenly, the final chunk will be the remaining
   * elements.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to process.
   * @param {number} [size=1] The length of each chunk
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the new array of chunks.
   * @example
   *
   * _.chunk(['a', 'b', 'c', 'd'], 2);
   * // => [['a', 'b'], ['c', 'd']]
   *
   * _.chunk(['a', 'b', 'c', 'd'], 3);
   * // => [['a', 'b', 'c'], ['d']]
   */
  function chunk(array, size, guard) {
    if (guard ? isIterateeCall(array, size, guard) : size === undefined) {
      size = 1
    } else {
      size = nativeMax(toInteger(size), 0)
    }
    var length = array == null ? 0 : array.length
    if (!length || size < 1) {
      return []
    }
    var index = 0,
      resIndex = 0,
      result = Array(nativeCeil(length / size))

    while (index < length) {
      result[resIndex++] = baseSlice(array, index, (index += size))
    }
    return result
  }

  /** Used as references for various `Number` constants. */
  var NAN$1 = 0 / 0

  /**
   * The base implementation of `_.toNumber` which doesn't ensure correct
   * conversions of binary, hexadecimal, or octal string values.
   *
   * @private
   * @param {*} value The value to process.
   * @returns {number} Returns the number.
   */
  function baseToNumber(value) {
    if (typeof value == 'number') {
      return value
    }
    if (isSymbol(value)) {
      return NAN$1
    }
    return +value
  }

  /**
   * A specialized version of `_.map` for arrays without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the new mapped array.
   */
  function arrayMap(array, iteratee) {
    var index = -1,
      length = array == null ? 0 : array.length,
      result = Array(length)

    while (++index < length) {
      result[index] = iteratee(array[index], index, array)
    }
    return result
  }

  /**
   * Checks if `value` is classified as an `Array` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an array, else `false`.
   * @example
   *
   * _.isArray([1, 2, 3]);
   * // => true
   *
   * _.isArray(document.body.children);
   * // => false
   *
   * _.isArray('abc');
   * // => false
   *
   * _.isArray(_.noop);
   * // => false
   */
  var isArray = Array.isArray

  /** Used as references for various `Number` constants. */
  var INFINITY$1 = 1 / 0

  /** Used to convert symbols to primitives and strings. */
  var symbolProto = Symbol$1 ? Symbol$1.prototype : undefined,
    symbolToString = symbolProto ? symbolProto.toString : undefined

  /**
   * The base implementation of `_.toString` which doesn't convert nullish
   * values to empty strings.
   *
   * @private
   * @param {*} value The value to process.
   * @returns {string} Returns the string.
   */
  function baseToString(value) {
    // Exit early for strings to avoid a performance hit in some environments.
    if (typeof value == 'string') {
      return value
    }
    if (isArray(value)) {
      // Recursively convert values (susceptible to call stack limits).
      return arrayMap(value, baseToString) + ''
    }
    if (isSymbol(value)) {
      return symbolToString ? symbolToString.call(value) : ''
    }
    var result = value + ''
    return result == '0' && 1 / value == -INFINITY$1 ? '-0' : result
  }

  /**
   * Creates a function that performs a mathematical operation on two values.
   *
   * @private
   * @param {Function} operator The function to perform the operation.
   * @param {number} [defaultValue] The value used for `undefined` arguments.
   * @returns {Function} Returns the new mathematical operation function.
   */
  function createMathOperation(operator, defaultValue) {
    return function(value, other) {
      var result
      if (value === undefined && other === undefined) {
        return defaultValue
      }
      if (value !== undefined) {
        result = value
      }
      if (other !== undefined) {
        if (result === undefined) {
          return other
        }
        if (typeof value == 'string' || typeof other == 'string') {
          value = baseToString(value)
          other = baseToString(other)
        } else {
          value = baseToNumber(value)
          other = baseToNumber(other)
        }
        result = operator(value, other)
      }
      return result
    }
  }

  /**
   * Adds two numbers.
   *
   * @static
   * @memberOf _
   * @since 3.4.0
   * @category Math
   * @param {number} augend The first number in an addition.
   * @param {number} addend The second number in an addition.
   * @returns {number} Returns the total.
   * @example
   *
   * _.add(6, 4);
   * // => 10
   */
  var add$1 = createMathOperation(function(augend, addend) {
    return augend + addend
  }, 0)

  /** Error message constants. */
  var FUNC_ERROR_TEXT = 'Expected a function'

  /**
   * The opposite of `_.before`; this method creates a function that invokes
   * `func` once it's called `n` or more times.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {number} n The number of calls before `func` is invoked.
   * @param {Function} func The function to restrict.
   * @returns {Function} Returns the new restricted function.
   * @example
   *
   * var saves = ['profile', 'settings'];
   *
   * var done = _.after(saves.length, function() {
   *   console.log('done saving!');
   * });
   *
   * _.forEach(saves, function(type) {
   *   asyncSave({ 'type': type, 'complete': done });
   * });
   * // => Logs 'done saving!' after the two async saves have completed.
   */
  function after(n, func) {
    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT)
    }
    n = toInteger(n)
    return function() {
      if (--n < 1) {
        return func.apply(this, arguments)
      }
    }
  }

  /**
   * This method returns the first argument it receives.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {*} value Any value.
   * @returns {*} Returns `value`.
   * @example
   *
   * var object = { 'a': 1 };
   *
   * console.log(_.identity(object) === object);
   * // => true
   */
  function identity(value) {
    return value
  }

  /** Used to detect overreaching core-js shims. */
  var coreJsData = root['__core-js_shared__']

  /** Used to detect methods masquerading as native. */
  var maskSrcKey = (function() {
    var uid = /[^.]+$/.exec(
      (coreJsData && coreJsData.keys && coreJsData.keys.IE_PROTO) || ''
    )
    return uid ? 'Symbol(src)_1.' + uid : ''
  })()

  /**
   * Checks if `func` has its source masked.
   *
   * @private
   * @param {Function} func The function to check.
   * @returns {boolean} Returns `true` if `func` is masked, else `false`.
   */
  function isMasked(func) {
    return !!maskSrcKey && maskSrcKey in func
  }

  /** Used for built-in method references. */
  var funcProto = Function.prototype

  /** Used to resolve the decompiled source of functions. */
  var funcToString = funcProto.toString

  /**
   * Converts `func` to its source code.
   *
   * @private
   * @param {Function} func The function to convert.
   * @returns {string} Returns the source code.
   */
  function toSource(func) {
    if (func != null) {
      try {
        return funcToString.call(func)
      } catch (e) {}
      try {
        return func + ''
      } catch (e) {}
    }
    return ''
  }

  /**
   * Used to match `RegExp`
   * [syntax characters](http://ecma-international.org/ecma-262/7.0/#sec-patterns).
   */
  var reRegExpChar = /[\\^$.*+?()[\]{}|]/g

  /** Used to detect host constructors (Safari). */
  var reIsHostCtor = /^\[object .+?Constructor\]$/

  /** Used for built-in method references. */
  var funcProto$1 = Function.prototype,
    objectProto$2 = Object.prototype

  /** Used to resolve the decompiled source of functions. */
  var funcToString$1 = funcProto$1.toString

  /** Used to check objects for own properties. */
  var hasOwnProperty$2 = objectProto$2.hasOwnProperty

  /** Used to detect if a method is native. */
  var reIsNative = RegExp(
    '^' +
      funcToString$1
        .call(hasOwnProperty$2)
        .replace(reRegExpChar, '\\$&')
        .replace(
          /hasOwnProperty|(function).*?(?=\\\()| for .+?(?=\\\])/g,
          '$1.*?'
        ) +
      '$'
  )

  /**
   * The base implementation of `_.isNative` without bad shim checks.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a native function,
   *  else `false`.
   */
  function baseIsNative(value) {
    if (!isObject(value) || isMasked(value)) {
      return false
    }
    var pattern = isFunction(value) ? reIsNative : reIsHostCtor
    return pattern.test(toSource(value))
  }

  /**
   * Gets the value at `key` of `object`.
   *
   * @private
   * @param {Object} [object] The object to query.
   * @param {string} key The key of the property to get.
   * @returns {*} Returns the property value.
   */
  function getValue(object, key) {
    return object == null ? undefined : object[key]
  }

  /**
   * Gets the native function at `key` of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {string} key The key of the method to get.
   * @returns {*} Returns the function if it's native, else `undefined`.
   */
  function getNative(object, key) {
    var value = getValue(object, key)
    return baseIsNative(value) ? value : undefined
  }

  /* Built-in method references that are verified to be native. */
  var WeakMap = getNative(root, 'WeakMap')

  /** Used to store function metadata. */
  var metaMap = WeakMap && new WeakMap()

  /**
   * The base implementation of `setData` without support for hot loop shorting.
   *
   * @private
   * @param {Function} func The function to associate metadata with.
   * @param {*} data The metadata.
   * @returns {Function} Returns `func`.
   */
  var baseSetData = !metaMap
    ? identity
    : function(func, data) {
        metaMap.set(func, data)
        return func
      }

  /** Built-in value references. */
  var objectCreate = Object.create

  /**
   * The base implementation of `_.create` without support for assigning
   * properties to the created object.
   *
   * @private
   * @param {Object} proto The object to inherit from.
   * @returns {Object} Returns the new object.
   */
  var baseCreate = (function() {
    function object() {}
    return function(proto) {
      if (!isObject(proto)) {
        return {}
      }
      if (objectCreate) {
        return objectCreate(proto)
      }
      object.prototype = proto
      var result = new object()
      object.prototype = undefined
      return result
    }
  })()

  /**
   * Creates a function that produces an instance of `Ctor` regardless of
   * whether it was invoked as part of a `new` expression or by `call` or `apply`.
   *
   * @private
   * @param {Function} Ctor The constructor to wrap.
   * @returns {Function} Returns the new wrapped function.
   */
  function createCtor(Ctor) {
    return function() {
      // Use a `switch` statement to work with class constructors. See
      // http://ecma-international.org/ecma-262/7.0/#sec-ecmascript-function-objects-call-thisargument-argumentslist
      // for more details.
      var args = arguments
      switch (args.length) {
        case 0:
          return new Ctor()
        case 1:
          return new Ctor(args[0])
        case 2:
          return new Ctor(args[0], args[1])
        case 3:
          return new Ctor(args[0], args[1], args[2])
        case 4:
          return new Ctor(args[0], args[1], args[2], args[3])
        case 5:
          return new Ctor(args[0], args[1], args[2], args[3], args[4])
        case 6:
          return new Ctor(args[0], args[1], args[2], args[3], args[4], args[5])
        case 7:
          return new Ctor(
            args[0],
            args[1],
            args[2],
            args[3],
            args[4],
            args[5],
            args[6]
          )
      }
      var thisBinding = baseCreate(Ctor.prototype),
        result = Ctor.apply(thisBinding, args)

      // Mimic the constructor's `return` behavior.
      // See https://es5.github.io/#x13.2.2 for more details.
      return isObject(result) ? result : thisBinding
    }
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG = 1

  /**
   * Creates a function that wraps `func` to invoke it with the optional `this`
   * binding of `thisArg`.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @param {*} [thisArg] The `this` binding of `func`.
   * @returns {Function} Returns the new wrapped function.
   */
  function createBind(func, bitmask, thisArg) {
    var isBind = bitmask & WRAP_BIND_FLAG,
      Ctor = createCtor(func)

    function wrapper() {
      var fn = this && this !== root && this instanceof wrapper ? Ctor : func
      return fn.apply(isBind ? thisArg : this, arguments)
    }
    return wrapper
  }

  /**
   * A faster alternative to `Function#apply`, this function invokes `func`
   * with the `this` binding of `thisArg` and the arguments of `args`.
   *
   * @private
   * @param {Function} func The function to invoke.
   * @param {*} thisArg The `this` binding of `func`.
   * @param {Array} args The arguments to invoke `func` with.
   * @returns {*} Returns the result of `func`.
   */
  function apply(func, thisArg, args) {
    switch (args.length) {
      case 0:
        return func.call(thisArg)
      case 1:
        return func.call(thisArg, args[0])
      case 2:
        return func.call(thisArg, args[0], args[1])
      case 3:
        return func.call(thisArg, args[0], args[1], args[2])
    }
    return func.apply(thisArg, args)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$1 = Math.max

  /**
   * Creates an array that is the composition of partially applied arguments,
   * placeholders, and provided arguments into a single array of arguments.
   *
   * @private
   * @param {Array} args The provided arguments.
   * @param {Array} partials The arguments to prepend to those provided.
   * @param {Array} holders The `partials` placeholder indexes.
   * @params {boolean} [isCurried] Specify composing for a curried function.
   * @returns {Array} Returns the new array of composed arguments.
   */
  function composeArgs(args, partials, holders, isCurried) {
    var argsIndex = -1,
      argsLength = args.length,
      holdersLength = holders.length,
      leftIndex = -1,
      leftLength = partials.length,
      rangeLength = nativeMax$1(argsLength - holdersLength, 0),
      result = Array(leftLength + rangeLength),
      isUncurried = !isCurried

    while (++leftIndex < leftLength) {
      result[leftIndex] = partials[leftIndex]
    }
    while (++argsIndex < holdersLength) {
      if (isUncurried || argsIndex < argsLength) {
        result[holders[argsIndex]] = args[argsIndex]
      }
    }
    while (rangeLength--) {
      result[leftIndex++] = args[argsIndex++]
    }
    return result
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$2 = Math.max

  /**
   * This function is like `composeArgs` except that the arguments composition
   * is tailored for `_.partialRight`.
   *
   * @private
   * @param {Array} args The provided arguments.
   * @param {Array} partials The arguments to append to those provided.
   * @param {Array} holders The `partials` placeholder indexes.
   * @params {boolean} [isCurried] Specify composing for a curried function.
   * @returns {Array} Returns the new array of composed arguments.
   */
  function composeArgsRight(args, partials, holders, isCurried) {
    var argsIndex = -1,
      argsLength = args.length,
      holdersIndex = -1,
      holdersLength = holders.length,
      rightIndex = -1,
      rightLength = partials.length,
      rangeLength = nativeMax$2(argsLength - holdersLength, 0),
      result = Array(rangeLength + rightLength),
      isUncurried = !isCurried

    while (++argsIndex < rangeLength) {
      result[argsIndex] = args[argsIndex]
    }
    var offset = argsIndex
    while (++rightIndex < rightLength) {
      result[offset + rightIndex] = partials[rightIndex]
    }
    while (++holdersIndex < holdersLength) {
      if (isUncurried || argsIndex < argsLength) {
        result[offset + holders[holdersIndex]] = args[argsIndex++]
      }
    }
    return result
  }

  /**
   * Gets the number of `placeholder` occurrences in `array`.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} placeholder The placeholder to search for.
   * @returns {number} Returns the placeholder count.
   */
  function countHolders(array, placeholder) {
    var length = array.length,
      result = 0

    while (length--) {
      if (array[length] === placeholder) {
        ++result
      }
    }
    return result
  }

  /**
   * The function whose prototype chain sequence wrappers inherit from.
   *
   * @private
   */
  function baseLodash() {
    // No operation performed.
  }

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH = 4294967295

  /**
   * Creates a lazy wrapper object which wraps `value` to enable lazy evaluation.
   *
   * @private
   * @constructor
   * @param {*} value The value to wrap.
   */
  function LazyWrapper(value) {
    this.__wrapped__ = value
    this.__actions__ = []
    this.__dir__ = 1
    this.__filtered__ = false
    this.__iteratees__ = []
    this.__takeCount__ = MAX_ARRAY_LENGTH
    this.__views__ = []
  }

  // Ensure `LazyWrapper` is an instance of `baseLodash`.
  LazyWrapper.prototype = baseCreate(baseLodash.prototype)
  LazyWrapper.prototype.constructor = LazyWrapper

  /**
   * This method returns `undefined`.
   *
   * @static
   * @memberOf _
   * @since 2.3.0
   * @category Util
   * @example
   *
   * _.times(2, _.noop);
   * // => [undefined, undefined]
   */
  function noop$1() {
    // No operation performed.
  }

  /**
   * Gets metadata for `func`.
   *
   * @private
   * @param {Function} func The function to query.
   * @returns {*} Returns the metadata for `func`.
   */
  var getData = !metaMap
    ? noop$1
    : function(func) {
        return metaMap.get(func)
      }

  /** Used to lookup unminified function names. */
  var realNames = {}

  /** Used for built-in method references. */
  var objectProto$3 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$3 = objectProto$3.hasOwnProperty

  /**
   * Gets the name of `func`.
   *
   * @private
   * @param {Function} func The function to query.
   * @returns {string} Returns the function name.
   */
  function getFuncName(func) {
    var result = func.name + '',
      array = realNames[result],
      length = hasOwnProperty$3.call(realNames, result) ? array.length : 0

    while (length--) {
      var data = array[length],
        otherFunc = data.func
      if (otherFunc == null || otherFunc == func) {
        return data.name
      }
    }
    return result
  }

  /**
   * The base constructor for creating `lodash` wrapper objects.
   *
   * @private
   * @param {*} value The value to wrap.
   * @param {boolean} [chainAll] Enable explicit method chain sequences.
   */
  function LodashWrapper(value, chainAll) {
    this.__wrapped__ = value
    this.__actions__ = []
    this.__chain__ = !!chainAll
    this.__index__ = 0
    this.__values__ = undefined
  }

  LodashWrapper.prototype = baseCreate(baseLodash.prototype)
  LodashWrapper.prototype.constructor = LodashWrapper

  /**
   * Copies the values of `source` to `array`.
   *
   * @private
   * @param {Array} source The array to copy values from.
   * @param {Array} [array=[]] The array to copy values to.
   * @returns {Array} Returns `array`.
   */
  function copyArray(source, array) {
    var index = -1,
      length = source.length

    array || (array = Array(length))
    while (++index < length) {
      array[index] = source[index]
    }
    return array
  }

  /**
   * Creates a clone of `wrapper`.
   *
   * @private
   * @param {Object} wrapper The wrapper to clone.
   * @returns {Object} Returns the cloned wrapper.
   */
  function wrapperClone(wrapper) {
    if (wrapper instanceof LazyWrapper) {
      return wrapper.clone()
    }
    var result = new LodashWrapper(wrapper.__wrapped__, wrapper.__chain__)
    result.__actions__ = copyArray(wrapper.__actions__)
    result.__index__ = wrapper.__index__
    result.__values__ = wrapper.__values__
    return result
  }

  /** Used for built-in method references. */
  var objectProto$4 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$4 = objectProto$4.hasOwnProperty

  /**
   * Creates a `lodash` object which wraps `value` to enable implicit method
   * chain sequences. Methods that operate on and return arrays, collections,
   * and functions can be chained together. Methods that retrieve a single value
   * or may return a primitive value will automatically end the chain sequence
   * and return the unwrapped value. Otherwise, the value must be unwrapped
   * with `_#value`.
   *
   * Explicit chain sequences, which must be unwrapped with `_#value`, may be
   * enabled using `_.chain`.
   *
   * The execution of chained methods is lazy, that is, it's deferred until
   * `_#value` is implicitly or explicitly called.
   *
   * Lazy evaluation allows several methods to support shortcut fusion.
   * Shortcut fusion is an optimization to merge iteratee calls; this avoids
   * the creation of intermediate arrays and can greatly reduce the number of
   * iteratee executions. Sections of a chain sequence qualify for shortcut
   * fusion if the section is applied to an array and iteratees accept only
   * one argument. The heuristic for whether a section qualifies for shortcut
   * fusion is subject to change.
   *
   * Chaining is supported in custom builds as long as the `_#value` method is
   * directly or indirectly included in the build.
   *
   * In addition to lodash methods, wrappers have `Array` and `String` methods.
   *
   * The wrapper `Array` methods are:
   * `concat`, `join`, `pop`, `push`, `shift`, `sort`, `splice`, and `unshift`
   *
   * The wrapper `String` methods are:
   * `replace` and `split`
   *
   * The wrapper methods that support shortcut fusion are:
   * `at`, `compact`, `drop`, `dropRight`, `dropWhile`, `filter`, `find`,
   * `findLast`, `head`, `initial`, `last`, `map`, `reject`, `reverse`, `slice`,
   * `tail`, `take`, `takeRight`, `takeRightWhile`, `takeWhile`, and `toArray`
   *
   * The chainable wrapper methods are:
   * `after`, `ary`, `assign`, `assignIn`, `assignInWith`, `assignWith`, `at`,
   * `before`, `bind`, `bindAll`, `bindKey`, `castArray`, `chain`, `chunk`,
   * `commit`, `compact`, `concat`, `conforms`, `constant`, `countBy`, `create`,
   * `curry`, `debounce`, `defaults`, `defaultsDeep`, `defer`, `delay`,
   * `difference`, `differenceBy`, `differenceWith`, `drop`, `dropRight`,
   * `dropRightWhile`, `dropWhile`, `extend`, `extendWith`, `fill`, `filter`,
   * `flatMap`, `flatMapDeep`, `flatMapDepth`, `flatten`, `flattenDeep`,
   * `flattenDepth`, `flip`, `flow`, `flowRight`, `fromPairs`, `functions`,
   * `functionsIn`, `groupBy`, `initial`, `intersection`, `intersectionBy`,
   * `intersectionWith`, `invert`, `invertBy`, `invokeMap`, `iteratee`, `keyBy`,
   * `keys`, `keysIn`, `map`, `mapKeys`, `mapValues`, `matches`, `matchesProperty`,
   * `memoize`, `merge`, `mergeWith`, `method`, `methodOf`, `mixin`, `negate`,
   * `nthArg`, `omit`, `omitBy`, `once`, `orderBy`, `over`, `overArgs`,
   * `overEvery`, `overSome`, `partial`, `partialRight`, `partition`, `pick`,
   * `pickBy`, `plant`, `property`, `propertyOf`, `pull`, `pullAll`, `pullAllBy`,
   * `pullAllWith`, `pullAt`, `push`, `range`, `rangeRight`, `rearg`, `reject`,
   * `remove`, `rest`, `reverse`, `sampleSize`, `set`, `setWith`, `shuffle`,
   * `slice`, `sort`, `sortBy`, `splice`, `spread`, `tail`, `take`, `takeRight`,
   * `takeRightWhile`, `takeWhile`, `tap`, `throttle`, `thru`, `toArray`,
   * `toPairs`, `toPairsIn`, `toPath`, `toPlainObject`, `transform`, `unary`,
   * `union`, `unionBy`, `unionWith`, `uniq`, `uniqBy`, `uniqWith`, `unset`,
   * `unshift`, `unzip`, `unzipWith`, `update`, `updateWith`, `values`,
   * `valuesIn`, `without`, `wrap`, `xor`, `xorBy`, `xorWith`, `zip`,
   * `zipObject`, `zipObjectDeep`, and `zipWith`
   *
   * The wrapper methods that are **not** chainable by default are:
   * `add`, `attempt`, `camelCase`, `capitalize`, `ceil`, `clamp`, `clone`,
   * `cloneDeep`, `cloneDeepWith`, `cloneWith`, `conformsTo`, `deburr`,
   * `defaultTo`, `divide`, `each`, `eachRight`, `endsWith`, `eq`, `escape`,
   * `escapeRegExp`, `every`, `find`, `findIndex`, `findKey`, `findLast`,
   * `findLastIndex`, `findLastKey`, `first`, `floor`, `forEach`, `forEachRight`,
   * `forIn`, `forInRight`, `forOwn`, `forOwnRight`, `get`, `gt`, `gte`, `has`,
   * `hasIn`, `head`, `identity`, `includes`, `indexOf`, `inRange`, `invoke`,
   * `isArguments`, `isArray`, `isArrayBuffer`, `isArrayLike`, `isArrayLikeObject`,
   * `isBoolean`, `isBuffer`, `isDate`, `isElement`, `isEmpty`, `isEqual`,
   * `isEqualWith`, `isError`, `isFinite`, `isFunction`, `isInteger`, `isLength`,
   * `isMap`, `isMatch`, `isMatchWith`, `isNaN`, `isNative`, `isNil`, `isNull`,
   * `isNumber`, `isObject`, `isObjectLike`, `isPlainObject`, `isRegExp`,
   * `isSafeInteger`, `isSet`, `isString`, `isUndefined`, `isTypedArray`,
   * `isWeakMap`, `isWeakSet`, `join`, `kebabCase`, `last`, `lastIndexOf`,
   * `lowerCase`, `lowerFirst`, `lt`, `lte`, `max`, `maxBy`, `mean`, `meanBy`,
   * `min`, `minBy`, `multiply`, `noConflict`, `noop`, `now`, `nth`, `pad`,
   * `padEnd`, `padStart`, `parseInt`, `pop`, `random`, `reduce`, `reduceRight`,
   * `repeat`, `result`, `round`, `runInContext`, `sample`, `shift`, `size`,
   * `snakeCase`, `some`, `sortedIndex`, `sortedIndexBy`, `sortedLastIndex`,
   * `sortedLastIndexBy`, `startCase`, `startsWith`, `stubArray`, `stubFalse`,
   * `stubObject`, `stubString`, `stubTrue`, `subtract`, `sum`, `sumBy`,
   * `template`, `times`, `toFinite`, `toInteger`, `toJSON`, `toLength`,
   * `toLower`, `toNumber`, `toSafeInteger`, `toString`, `toUpper`, `trim`,
   * `trimEnd`, `trimStart`, `truncate`, `unescape`, `uniqueId`, `upperCase`,
   * `upperFirst`, `value`, and `words`
   *
   * @name _
   * @constructor
   * @category Seq
   * @param {*} value The value to wrap in a `lodash` instance.
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * function square(n) {
   *   return n * n;
   * }
   *
   * var wrapped = _([1, 2, 3]);
   *
   * // Returns an unwrapped value.
   * wrapped.reduce(_.add);
   * // => 6
   *
   * // Returns a wrapped value.
   * var squares = wrapped.map(square);
   *
   * _.isArray(squares);
   * // => false
   *
   * _.isArray(squares.value());
   * // => true
   */
  function lodash(value) {
    if (
      isObjectLike(value) &&
      !isArray(value) &&
      !(value instanceof LazyWrapper)
    ) {
      if (value instanceof LodashWrapper) {
        return value
      }
      if (hasOwnProperty$4.call(value, '__wrapped__')) {
        return wrapperClone(value)
      }
    }
    return new LodashWrapper(value)
  }

  // Ensure wrappers are instances of `baseLodash`.
  lodash.prototype = baseLodash.prototype
  lodash.prototype.constructor = lodash

  /**
   * Checks if `func` has a lazy counterpart.
   *
   * @private
   * @param {Function} func The function to check.
   * @returns {boolean} Returns `true` if `func` has a lazy counterpart,
   *  else `false`.
   */
  function isLaziable(func) {
    var funcName = getFuncName(func),
      other = lodash[funcName]

    if (typeof other != 'function' || !(funcName in LazyWrapper.prototype)) {
      return false
    }
    if (func === other) {
      return true
    }
    var data = getData(other)
    return !!data && func === data[0]
  }

  /** Used to detect hot functions by number of calls within a span of milliseconds. */
  var HOT_COUNT = 800,
    HOT_SPAN = 16

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeNow = Date.now

  /**
   * Creates a function that'll short out and invoke `identity` instead
   * of `func` when it's called `HOT_COUNT` or more times in `HOT_SPAN`
   * milliseconds.
   *
   * @private
   * @param {Function} func The function to restrict.
   * @returns {Function} Returns the new shortable function.
   */
  function shortOut(func) {
    var count = 0,
      lastCalled = 0

    return function() {
      var stamp = nativeNow(),
        remaining = HOT_SPAN - (stamp - lastCalled)

      lastCalled = stamp
      if (remaining > 0) {
        if (++count >= HOT_COUNT) {
          return arguments[0]
        }
      } else {
        count = 0
      }
      return func.apply(undefined, arguments)
    }
  }

  /**
   * Sets metadata for `func`.
   *
   * **Note:** If this function becomes hot, i.e. is invoked a lot in a short
   * period of time, it will trip its breaker and transition to an identity
   * function to avoid garbage collection pauses in V8. See
   * [V8 issue 2070](https://bugs.chromium.org/p/v8/issues/detail?id=2070)
   * for more details.
   *
   * @private
   * @param {Function} func The function to associate metadata with.
   * @param {*} data The metadata.
   * @returns {Function} Returns `func`.
   */
  var setData = shortOut(baseSetData)

  /** Used to match wrap detail comments. */
  var reWrapDetails = /\{\n\/\* \[wrapped with (.+)\] \*/,
    reSplitDetails = /,? & /

  /**
   * Extracts wrapper details from the `source` body comment.
   *
   * @private
   * @param {string} source The source to inspect.
   * @returns {Array} Returns the wrapper details.
   */
  function getWrapDetails(source) {
    var match = source.match(reWrapDetails)
    return match ? match[1].split(reSplitDetails) : []
  }

  /** Used to match wrap detail comments. */
  var reWrapComment = /\{(?:\n\/\* \[wrapped with .+\] \*\/)?\n?/

  /**
   * Inserts wrapper `details` in a comment at the top of the `source` body.
   *
   * @private
   * @param {string} source The source to modify.
   * @returns {Array} details The details to insert.
   * @returns {string} Returns the modified source.
   */
  function insertWrapDetails(source, details) {
    var length = details.length
    if (!length) {
      return source
    }
    var lastIndex = length - 1
    details[lastIndex] = (length > 1 ? '& ' : '') + details[lastIndex]
    details = details.join(length > 2 ? ', ' : ' ')
    return source.replace(
      reWrapComment,
      '{\n/* [wrapped with ' + details + '] */\n'
    )
  }

  /**
   * Creates a function that returns `value`.
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Util
   * @param {*} value The value to return from the new function.
   * @returns {Function} Returns the new constant function.
   * @example
   *
   * var objects = _.times(2, _.constant({ 'a': 1 }));
   *
   * console.log(objects);
   * // => [{ 'a': 1 }, { 'a': 1 }]
   *
   * console.log(objects[0] === objects[1]);
   * // => true
   */
  function constant(value) {
    return function() {
      return value
    }
  }

  var defineProperty = (function() {
    try {
      var func = getNative(Object, 'defineProperty')
      func({}, '', {})
      return func
    } catch (e) {}
  })()

  /**
   * The base implementation of `setToString` without support for hot loop shorting.
   *
   * @private
   * @param {Function} func The function to modify.
   * @param {Function} string The `toString` result.
   * @returns {Function} Returns `func`.
   */
  var baseSetToString = !defineProperty
    ? identity
    : function(func, string) {
        return defineProperty(func, 'toString', {
          configurable: true,
          enumerable: false,
          value: constant(string),
          writable: true,
        })
      }

  /**
   * Sets the `toString` method of `func` to return `string`.
   *
   * @private
   * @param {Function} func The function to modify.
   * @param {Function} string The `toString` result.
   * @returns {Function} Returns `func`.
   */
  var setToString = shortOut(baseSetToString)

  /**
   * A specialized version of `_.forEach` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns `array`.
   */
  function arrayEach(array, iteratee) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      if (iteratee(array[index], index, array) === false) {
        break
      }
    }
    return array
  }

  /**
   * The base implementation of `_.findIndex` and `_.findLastIndex` without
   * support for iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {Function} predicate The function invoked per iteration.
   * @param {number} fromIndex The index to search from.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseFindIndex(array, predicate, fromIndex, fromRight) {
    var length = array.length,
      index = fromIndex + (fromRight ? 1 : -1)

    while (fromRight ? index-- : ++index < length) {
      if (predicate(array[index], index, array)) {
        return index
      }
    }
    return -1
  }

  /**
   * The base implementation of `_.isNaN` without support for number objects.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is `NaN`, else `false`.
   */
  function baseIsNaN(value) {
    return value !== value
  }

  /**
   * A specialized version of `_.indexOf` which performs strict equality
   * comparisons of values, i.e. `===`.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function strictIndexOf(array, value, fromIndex) {
    var index = fromIndex - 1,
      length = array.length

    while (++index < length) {
      if (array[index] === value) {
        return index
      }
    }
    return -1
  }

  /**
   * The base implementation of `_.indexOf` without `fromIndex` bounds checks.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseIndexOf(array, value, fromIndex) {
    return value === value
      ? strictIndexOf(array, value, fromIndex)
      : baseFindIndex(array, baseIsNaN, fromIndex)
  }

  /**
   * A specialized version of `_.includes` for arrays without support for
   * specifying an index to search from.
   *
   * @private
   * @param {Array} [array] The array to inspect.
   * @param {*} target The value to search for.
   * @returns {boolean} Returns `true` if `target` is found, else `false`.
   */
  function arrayIncludes(array, value) {
    var length = array == null ? 0 : array.length
    return !!length && baseIndexOf(array, value, 0) > -1
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$1 = 1,
    WRAP_BIND_KEY_FLAG = 2,
    WRAP_CURRY_FLAG = 8,
    WRAP_CURRY_RIGHT_FLAG = 16,
    WRAP_PARTIAL_FLAG = 32,
    WRAP_PARTIAL_RIGHT_FLAG = 64,
    WRAP_ARY_FLAG = 128,
    WRAP_REARG_FLAG = 256,
    WRAP_FLIP_FLAG = 512

  /** Used to associate wrap methods with their bit flags. */
  var wrapFlags = [
    ['ary', WRAP_ARY_FLAG],
    ['bind', WRAP_BIND_FLAG$1],
    ['bindKey', WRAP_BIND_KEY_FLAG],
    ['curry', WRAP_CURRY_FLAG],
    ['curryRight', WRAP_CURRY_RIGHT_FLAG],
    ['flip', WRAP_FLIP_FLAG],
    ['partial', WRAP_PARTIAL_FLAG],
    ['partialRight', WRAP_PARTIAL_RIGHT_FLAG],
    ['rearg', WRAP_REARG_FLAG],
  ]

  /**
   * Updates wrapper `details` based on `bitmask` flags.
   *
   * @private
   * @returns {Array} details The details to modify.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @returns {Array} Returns `details`.
   */
  function updateWrapDetails(details, bitmask) {
    arrayEach(wrapFlags, function(pair) {
      var value = '_.' + pair[0]
      if (bitmask & pair[1] && !arrayIncludes(details, value)) {
        details.push(value)
      }
    })
    return details.sort()
  }

  /**
   * Sets the `toString` method of `wrapper` to mimic the source of `reference`
   * with wrapper details in a comment at the top of the source body.
   *
   * @private
   * @param {Function} wrapper The function to modify.
   * @param {Function} reference The reference function.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @returns {Function} Returns `wrapper`.
   */
  function setWrapToString(wrapper, reference, bitmask) {
    var source = reference + ''
    return setToString(
      wrapper,
      insertWrapDetails(
        source,
        updateWrapDetails(getWrapDetails(source), bitmask)
      )
    )
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$2 = 1,
    WRAP_BIND_KEY_FLAG$1 = 2,
    WRAP_CURRY_BOUND_FLAG = 4,
    WRAP_CURRY_FLAG$1 = 8,
    WRAP_PARTIAL_FLAG$1 = 32,
    WRAP_PARTIAL_RIGHT_FLAG$1 = 64

  /**
   * Creates a function that wraps `func` to continue currying.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @param {Function} wrapFunc The function to create the `func` wrapper.
   * @param {*} placeholder The placeholder value.
   * @param {*} [thisArg] The `this` binding of `func`.
   * @param {Array} [partials] The arguments to prepend to those provided to
   *  the new function.
   * @param {Array} [holders] The `partials` placeholder indexes.
   * @param {Array} [argPos] The argument positions of the new function.
   * @param {number} [ary] The arity cap of `func`.
   * @param {number} [arity] The arity of `func`.
   * @returns {Function} Returns the new wrapped function.
   */
  function createRecurry(
    func,
    bitmask,
    wrapFunc,
    placeholder,
    thisArg,
    partials,
    holders,
    argPos,
    ary,
    arity
  ) {
    var isCurry = bitmask & WRAP_CURRY_FLAG$1,
      newHolders = isCurry ? holders : undefined,
      newHoldersRight = isCurry ? undefined : holders,
      newPartials = isCurry ? partials : undefined,
      newPartialsRight = isCurry ? undefined : partials

    bitmask |= isCurry ? WRAP_PARTIAL_FLAG$1 : WRAP_PARTIAL_RIGHT_FLAG$1
    bitmask &= ~(isCurry ? WRAP_PARTIAL_RIGHT_FLAG$1 : WRAP_PARTIAL_FLAG$1)

    if (!(bitmask & WRAP_CURRY_BOUND_FLAG)) {
      bitmask &= ~(WRAP_BIND_FLAG$2 | WRAP_BIND_KEY_FLAG$1)
    }
    var newData = [
      func,
      bitmask,
      thisArg,
      newPartials,
      newHolders,
      newPartialsRight,
      newHoldersRight,
      argPos,
      ary,
      arity,
    ]

    var result = wrapFunc.apply(undefined, newData)
    if (isLaziable(func)) {
      setData(result, newData)
    }
    result.placeholder = placeholder
    return setWrapToString(result, func, bitmask)
  }

  /**
   * Gets the argument placeholder value for `func`.
   *
   * @private
   * @param {Function} func The function to inspect.
   * @returns {*} Returns the placeholder value.
   */
  function getHolder(func) {
    var object = func
    return object.placeholder
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin = Math.min

  /**
   * Reorder `array` according to the specified indexes where the element at
   * the first index is assigned as the first element, the element at
   * the second index is assigned as the second element, and so on.
   *
   * @private
   * @param {Array} array The array to reorder.
   * @param {Array} indexes The arranged array indexes.
   * @returns {Array} Returns `array`.
   */
  function reorder(array, indexes) {
    var arrLength = array.length,
      length = nativeMin(indexes.length, arrLength),
      oldArray = copyArray(array)

    while (length--) {
      var index = indexes[length]
      array[length] = isIndex(index, arrLength) ? oldArray[index] : undefined
    }
    return array
  }

  /** Used as the internal argument placeholder. */
  var PLACEHOLDER = '__lodash_placeholder__'

  /**
   * Replaces all `placeholder` elements in `array` with an internal placeholder
   * and returns an array of their indexes.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {*} placeholder The placeholder to replace.
   * @returns {Array} Returns the new array of placeholder indexes.
   */
  function replaceHolders(array, placeholder) {
    var index = -1,
      length = array.length,
      resIndex = 0,
      result = []

    while (++index < length) {
      var value = array[index]
      if (value === placeholder || value === PLACEHOLDER) {
        array[index] = PLACEHOLDER
        result[resIndex++] = index
      }
    }
    return result
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$3 = 1,
    WRAP_BIND_KEY_FLAG$2 = 2,
    WRAP_CURRY_FLAG$2 = 8,
    WRAP_CURRY_RIGHT_FLAG$1 = 16,
    WRAP_ARY_FLAG$1 = 128,
    WRAP_FLIP_FLAG$1 = 512

  /**
   * Creates a function that wraps `func` to invoke it with optional `this`
   * binding of `thisArg`, partial application, and currying.
   *
   * @private
   * @param {Function|string} func The function or method name to wrap.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @param {*} [thisArg] The `this` binding of `func`.
   * @param {Array} [partials] The arguments to prepend to those provided to
   *  the new function.
   * @param {Array} [holders] The `partials` placeholder indexes.
   * @param {Array} [partialsRight] The arguments to append to those provided
   *  to the new function.
   * @param {Array} [holdersRight] The `partialsRight` placeholder indexes.
   * @param {Array} [argPos] The argument positions of the new function.
   * @param {number} [ary] The arity cap of `func`.
   * @param {number} [arity] The arity of `func`.
   * @returns {Function} Returns the new wrapped function.
   */
  function createHybrid(
    func,
    bitmask,
    thisArg,
    partials,
    holders,
    partialsRight,
    holdersRight,
    argPos,
    ary,
    arity
  ) {
    var isAry = bitmask & WRAP_ARY_FLAG$1,
      isBind = bitmask & WRAP_BIND_FLAG$3,
      isBindKey = bitmask & WRAP_BIND_KEY_FLAG$2,
      isCurried = bitmask & (WRAP_CURRY_FLAG$2 | WRAP_CURRY_RIGHT_FLAG$1),
      isFlip = bitmask & WRAP_FLIP_FLAG$1,
      Ctor = isBindKey ? undefined : createCtor(func)

    function wrapper() {
      var length = arguments.length,
        args = Array(length),
        index = length

      while (index--) {
        args[index] = arguments[index]
      }
      if (isCurried) {
        var placeholder = getHolder(wrapper),
          holdersCount = countHolders(args, placeholder)
      }
      if (partials) {
        args = composeArgs(args, partials, holders, isCurried)
      }
      if (partialsRight) {
        args = composeArgsRight(args, partialsRight, holdersRight, isCurried)
      }
      length -= holdersCount
      if (isCurried && length < arity) {
        var newHolders = replaceHolders(args, placeholder)
        return createRecurry(
          func,
          bitmask,
          createHybrid,
          wrapper.placeholder,
          thisArg,
          args,
          newHolders,
          argPos,
          ary,
          arity - length
        )
      }
      var thisBinding = isBind ? thisArg : this,
        fn = isBindKey ? thisBinding[func] : func

      length = args.length
      if (argPos) {
        args = reorder(args, argPos)
      } else if (isFlip && length > 1) {
        args.reverse()
      }
      if (isAry && ary < length) {
        args.length = ary
      }
      if (this && this !== root && this instanceof wrapper) {
        fn = Ctor || createCtor(fn)
      }
      return fn.apply(thisBinding, args)
    }
    return wrapper
  }

  /**
   * Creates a function that wraps `func` to enable currying.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @param {number} arity The arity of `func`.
   * @returns {Function} Returns the new wrapped function.
   */
  function createCurry(func, bitmask, arity) {
    var Ctor = createCtor(func)

    function wrapper() {
      var length = arguments.length,
        args = Array(length),
        index = length,
        placeholder = getHolder(wrapper)

      while (index--) {
        args[index] = arguments[index]
      }
      var holders =
        length < 3 &&
        args[0] !== placeholder &&
        args[length - 1] !== placeholder
          ? []
          : replaceHolders(args, placeholder)

      length -= holders.length
      if (length < arity) {
        return createRecurry(
          func,
          bitmask,
          createHybrid,
          wrapper.placeholder,
          undefined,
          args,
          holders,
          undefined,
          undefined,
          arity - length
        )
      }
      var fn = this && this !== root && this instanceof wrapper ? Ctor : func
      return apply(fn, this, args)
    }
    return wrapper
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$4 = 1

  /**
   * Creates a function that wraps `func` to invoke it with the `this` binding
   * of `thisArg` and `partials` prepended to the arguments it receives.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {number} bitmask The bitmask flags. See `createWrap` for more details.
   * @param {*} thisArg The `this` binding of `func`.
   * @param {Array} partials The arguments to prepend to those provided to
   *  the new function.
   * @returns {Function} Returns the new wrapped function.
   */
  function createPartial(func, bitmask, thisArg, partials) {
    var isBind = bitmask & WRAP_BIND_FLAG$4,
      Ctor = createCtor(func)

    function wrapper() {
      var argsIndex = -1,
        argsLength = arguments.length,
        leftIndex = -1,
        leftLength = partials.length,
        args = Array(leftLength + argsLength),
        fn = this && this !== root && this instanceof wrapper ? Ctor : func

      while (++leftIndex < leftLength) {
        args[leftIndex] = partials[leftIndex]
      }
      while (argsLength--) {
        args[leftIndex++] = arguments[++argsIndex]
      }
      return apply(fn, isBind ? thisArg : this, args)
    }
    return wrapper
  }

  /** Used as the internal argument placeholder. */
  var PLACEHOLDER$1 = '__lodash_placeholder__'

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$5 = 1,
    WRAP_BIND_KEY_FLAG$3 = 2,
    WRAP_CURRY_BOUND_FLAG$1 = 4,
    WRAP_CURRY_FLAG$3 = 8,
    WRAP_ARY_FLAG$2 = 128,
    WRAP_REARG_FLAG$1 = 256

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin$1 = Math.min

  /**
   * Merges the function metadata of `source` into `data`.
   *
   * Merging metadata reduces the number of wrappers used to invoke a function.
   * This is possible because methods like `_.bind`, `_.curry`, and `_.partial`
   * may be applied regardless of execution order. Methods like `_.ary` and
   * `_.rearg` modify function arguments, making the order in which they are
   * executed important, preventing the merging of metadata. However, we make
   * an exception for a safe combined case where curried functions have `_.ary`
   * and or `_.rearg` applied.
   *
   * @private
   * @param {Array} data The destination metadata.
   * @param {Array} source The source metadata.
   * @returns {Array} Returns `data`.
   */
  function mergeData(data, source) {
    var bitmask = data[1],
      srcBitmask = source[1],
      newBitmask = bitmask | srcBitmask,
      isCommon =
        newBitmask < (WRAP_BIND_FLAG$5 | WRAP_BIND_KEY_FLAG$3 | WRAP_ARY_FLAG$2)

    var isCombo =
      (srcBitmask == WRAP_ARY_FLAG$2 && bitmask == WRAP_CURRY_FLAG$3) ||
      (srcBitmask == WRAP_ARY_FLAG$2 &&
        bitmask == WRAP_REARG_FLAG$1 &&
        data[7].length <= source[8]) ||
      (srcBitmask == (WRAP_ARY_FLAG$2 | WRAP_REARG_FLAG$1) &&
        source[7].length <= source[8] &&
        bitmask == WRAP_CURRY_FLAG$3)

    // Exit early if metadata can't be merged.
    if (!(isCommon || isCombo)) {
      return data
    }
    // Use source `thisArg` if available.
    if (srcBitmask & WRAP_BIND_FLAG$5) {
      data[2] = source[2]
      // Set when currying a bound function.
      newBitmask |= bitmask & WRAP_BIND_FLAG$5 ? 0 : WRAP_CURRY_BOUND_FLAG$1
    }
    // Compose partial arguments.
    var value = source[3]
    if (value) {
      var partials = data[3]
      data[3] = partials ? composeArgs(partials, value, source[4]) : value
      data[4] = partials ? replaceHolders(data[3], PLACEHOLDER$1) : source[4]
    }
    // Compose partial right arguments.
    value = source[5]
    if (value) {
      partials = data[5]
      data[5] = partials ? composeArgsRight(partials, value, source[6]) : value
      data[6] = partials ? replaceHolders(data[5], PLACEHOLDER$1) : source[6]
    }
    // Use source `argPos` if available.
    value = source[7]
    if (value) {
      data[7] = value
    }
    // Use source `ary` if it's smaller.
    if (srcBitmask & WRAP_ARY_FLAG$2) {
      data[8] = data[8] == null ? source[8] : nativeMin$1(data[8], source[8])
    }
    // Use source `arity` if one is not provided.
    if (data[9] == null) {
      data[9] = source[9]
    }
    // Use source `func` and merge bitmasks.
    data[0] = source[0]
    data[1] = newBitmask

    return data
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$1 = 'Expected a function'

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$6 = 1,
    WRAP_BIND_KEY_FLAG$4 = 2,
    WRAP_CURRY_FLAG$4 = 8,
    WRAP_CURRY_RIGHT_FLAG$2 = 16,
    WRAP_PARTIAL_FLAG$2 = 32,
    WRAP_PARTIAL_RIGHT_FLAG$2 = 64

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$3 = Math.max

  /**
   * Creates a function that either curries or invokes `func` with optional
   * `this` binding and partially applied arguments.
   *
   * @private
   * @param {Function|string} func The function or method name to wrap.
   * @param {number} bitmask The bitmask flags.
   *    1 - `_.bind`
   *    2 - `_.bindKey`
   *    4 - `_.curry` or `_.curryRight` of a bound function
   *    8 - `_.curry`
   *   16 - `_.curryRight`
   *   32 - `_.partial`
   *   64 - `_.partialRight`
   *  128 - `_.rearg`
   *  256 - `_.ary`
   *  512 - `_.flip`
   * @param {*} [thisArg] The `this` binding of `func`.
   * @param {Array} [partials] The arguments to be partially applied.
   * @param {Array} [holders] The `partials` placeholder indexes.
   * @param {Array} [argPos] The argument positions of the new function.
   * @param {number} [ary] The arity cap of `func`.
   * @param {number} [arity] The arity of `func`.
   * @returns {Function} Returns the new wrapped function.
   */
  function createWrap(
    func,
    bitmask,
    thisArg,
    partials,
    holders,
    argPos,
    ary,
    arity
  ) {
    var isBindKey = bitmask & WRAP_BIND_KEY_FLAG$4
    if (!isBindKey && typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$1)
    }
    var length = partials ? partials.length : 0
    if (!length) {
      bitmask &= ~(WRAP_PARTIAL_FLAG$2 | WRAP_PARTIAL_RIGHT_FLAG$2)
      partials = holders = undefined
    }
    ary = ary === undefined ? ary : nativeMax$3(toInteger(ary), 0)
    arity = arity === undefined ? arity : toInteger(arity)
    length -= holders ? holders.length : 0

    if (bitmask & WRAP_PARTIAL_RIGHT_FLAG$2) {
      var partialsRight = partials,
        holdersRight = holders

      partials = holders = undefined
    }
    var data = isBindKey ? undefined : getData(func)

    var newData = [
      func,
      bitmask,
      thisArg,
      partials,
      holders,
      partialsRight,
      holdersRight,
      argPos,
      ary,
      arity,
    ]

    if (data) {
      mergeData(newData, data)
    }
    func = newData[0]
    bitmask = newData[1]
    thisArg = newData[2]
    partials = newData[3]
    holders = newData[4]
    arity = newData[9] =
      newData[9] === undefined
        ? isBindKey
          ? 0
          : func.length
        : nativeMax$3(newData[9] - length, 0)

    if (!arity && bitmask & (WRAP_CURRY_FLAG$4 | WRAP_CURRY_RIGHT_FLAG$2)) {
      bitmask &= ~(WRAP_CURRY_FLAG$4 | WRAP_CURRY_RIGHT_FLAG$2)
    }
    if (!bitmask || bitmask == WRAP_BIND_FLAG$6) {
      var result = createBind(func, bitmask, thisArg)
    } else if (
      bitmask == WRAP_CURRY_FLAG$4 ||
      bitmask == WRAP_CURRY_RIGHT_FLAG$2
    ) {
      result = createCurry(func, bitmask, arity)
    } else if (
      (bitmask == WRAP_PARTIAL_FLAG$2 ||
        bitmask == (WRAP_BIND_FLAG$6 | WRAP_PARTIAL_FLAG$2)) &&
      !holders.length
    ) {
      result = createPartial(func, bitmask, thisArg, partials)
    } else {
      result = createHybrid.apply(undefined, newData)
    }
    var setter = data ? baseSetData : setData
    return setWrapToString(setter(result, newData), func, bitmask)
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_ARY_FLAG$3 = 128

  /**
   * Creates a function that invokes `func`, with up to `n` arguments,
   * ignoring any additional arguments.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Function
   * @param {Function} func The function to cap arguments for.
   * @param {number} [n=func.length] The arity cap.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Function} Returns the new capped function.
   * @example
   *
   * _.map(['6', '8', '10'], _.ary(parseInt, 1));
   * // => [6, 8, 10]
   */
  function ary(func, n, guard) {
    n = guard ? undefined : n
    n = func && n == null ? func.length : n
    return createWrap(
      func,
      WRAP_ARY_FLAG$3,
      undefined,
      undefined,
      undefined,
      undefined,
      n
    )
  }

  /**
   * The base implementation of `assignValue` and `assignMergeValue` without
   * value checks.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {string} key The key of the property to assign.
   * @param {*} value The value to assign.
   */
  function baseAssignValue(object, key, value) {
    if (key == '__proto__' && defineProperty) {
      defineProperty(object, key, {
        configurable: true,
        enumerable: true,
        value: value,
        writable: true,
      })
    } else {
      object[key] = value
    }
  }

  /** Used for built-in method references. */
  var objectProto$5 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$5 = objectProto$5.hasOwnProperty

  /**
   * Assigns `value` to `key` of `object` if the existing value is not equivalent
   * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {string} key The key of the property to assign.
   * @param {*} value The value to assign.
   */
  function assignValue(object, key, value) {
    var objValue = object[key]
    if (
      !(hasOwnProperty$5.call(object, key) && eq$1(objValue, value)) ||
      (value === undefined && !(key in object))
    ) {
      baseAssignValue(object, key, value)
    }
  }

  /**
   * Copies properties of `source` to `object`.
   *
   * @private
   * @param {Object} source The object to copy properties from.
   * @param {Array} props The property identifiers to copy.
   * @param {Object} [object={}] The object to copy properties to.
   * @param {Function} [customizer] The function to customize copied values.
   * @returns {Object} Returns `object`.
   */
  function copyObject(source, props, object, customizer) {
    var isNew = !object
    object || (object = {})

    var index = -1,
      length = props.length

    while (++index < length) {
      var key = props[index]

      var newValue = customizer
        ? customizer(object[key], source[key], key, object, source)
        : undefined

      if (newValue === undefined) {
        newValue = source[key]
      }
      if (isNew) {
        baseAssignValue(object, key, newValue)
      } else {
        assignValue(object, key, newValue)
      }
    }
    return object
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$4 = Math.max

  /**
   * A specialized version of `baseRest` which transforms the rest array.
   *
   * @private
   * @param {Function} func The function to apply a rest parameter to.
   * @param {number} [start=func.length-1] The start position of the rest parameter.
   * @param {Function} transform The rest array transform.
   * @returns {Function} Returns the new function.
   */
  function overRest(func, start, transform) {
    start = nativeMax$4(start === undefined ? func.length - 1 : start, 0)
    return function() {
      var args = arguments,
        index = -1,
        length = nativeMax$4(args.length - start, 0),
        array = Array(length)

      while (++index < length) {
        array[index] = args[start + index]
      }
      index = -1
      var otherArgs = Array(start + 1)
      while (++index < start) {
        otherArgs[index] = args[index]
      }
      otherArgs[start] = transform(array)
      return apply(func, this, otherArgs)
    }
  }

  /**
   * The base implementation of `_.rest` which doesn't validate or coerce arguments.
   *
   * @private
   * @param {Function} func The function to apply a rest parameter to.
   * @param {number} [start=func.length-1] The start position of the rest parameter.
   * @returns {Function} Returns the new function.
   */
  function baseRest(func, start) {
    return setToString(overRest(func, start, identity), func + '')
  }

  /**
   * Creates a function like `_.assign`.
   *
   * @private
   * @param {Function} assigner The function to assign values.
   * @returns {Function} Returns the new assigner function.
   */
  function createAssigner(assigner) {
    return baseRest(function(object, sources) {
      var index = -1,
        length = sources.length,
        customizer = length > 1 ? sources[length - 1] : undefined,
        guard = length > 2 ? sources[2] : undefined

      customizer =
        assigner.length > 3 && typeof customizer == 'function'
          ? (length--, customizer)
          : undefined

      if (guard && isIterateeCall(sources[0], sources[1], guard)) {
        customizer = length < 3 ? undefined : customizer
        length = 1
      }
      object = Object(object)
      while (++index < length) {
        var source = sources[index]
        if (source) {
          assigner(object, source, index, customizer)
        }
      }
      return object
    })
  }

  /** Used for built-in method references. */
  var objectProto$6 = Object.prototype

  /**
   * Checks if `value` is likely a prototype object.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a prototype, else `false`.
   */
  function isPrototype(value) {
    var Ctor = value && value.constructor,
      proto = (typeof Ctor == 'function' && Ctor.prototype) || objectProto$6

    return value === proto
  }

  /**
   * The base implementation of `_.times` without support for iteratee shorthands
   * or max array length checks.
   *
   * @private
   * @param {number} n The number of times to invoke `iteratee`.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the array of results.
   */
  function baseTimes(n, iteratee) {
    var index = -1,
      result = Array(n)

    while (++index < n) {
      result[index] = iteratee(index)
    }
    return result
  }

  /** `Object#toString` result references. */
  var argsTag = '[object Arguments]'

  /**
   * The base implementation of `_.isArguments`.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an `arguments` object,
   */
  function baseIsArguments(value) {
    return isObjectLike(value) && baseGetTag(value) == argsTag
  }

  /** Used for built-in method references. */
  var objectProto$7 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$6 = objectProto$7.hasOwnProperty

  /** Built-in value references. */
  var propertyIsEnumerable = objectProto$7.propertyIsEnumerable

  /**
   * Checks if `value` is likely an `arguments` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an `arguments` object,
   *  else `false`.
   * @example
   *
   * _.isArguments(function() { return arguments; }());
   * // => true
   *
   * _.isArguments([1, 2, 3]);
   * // => false
   */
  var isArguments = baseIsArguments(
    (function() {
      return arguments
    })()
  )
    ? baseIsArguments
    : function(value) {
        return (
          isObjectLike(value) &&
          hasOwnProperty$6.call(value, 'callee') &&
          !propertyIsEnumerable.call(value, 'callee')
        )
      }

  /**
   * This method returns `false`.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {boolean} Returns `false`.
   * @example
   *
   * _.times(2, _.stubFalse);
   * // => [false, false]
   */
  function stubFalse() {
    return false
  }

  /** Detect free variable `exports`. */
  var freeExports =
    typeof exports == 'object' && exports && !exports.nodeType && exports

  /** Detect free variable `module`. */
  var freeModule =
    freeExports &&
    typeof module == 'object' &&
    module &&
    !module.nodeType &&
    module

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports = freeModule && freeModule.exports === freeExports

  /** Built-in value references. */
  var Buffer = moduleExports ? root.Buffer : undefined

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeIsBuffer = Buffer ? Buffer.isBuffer : undefined

  /**
   * Checks if `value` is a buffer.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a buffer, else `false`.
   * @example
   *
   * _.isBuffer(new Buffer(2));
   * // => true
   *
   * _.isBuffer(new Uint8Array(2));
   * // => false
   */
  var isBuffer = nativeIsBuffer || stubFalse

  /** `Object#toString` result references. */
  var argsTag$1 = '[object Arguments]',
    arrayTag = '[object Array]',
    boolTag = '[object Boolean]',
    dateTag = '[object Date]',
    errorTag = '[object Error]',
    funcTag$1 = '[object Function]',
    mapTag = '[object Map]',
    numberTag = '[object Number]',
    objectTag = '[object Object]',
    regexpTag = '[object RegExp]',
    setTag = '[object Set]',
    stringTag = '[object String]',
    weakMapTag = '[object WeakMap]'

  var arrayBufferTag = '[object ArrayBuffer]',
    dataViewTag = '[object DataView]',
    float32Tag = '[object Float32Array]',
    float64Tag = '[object Float64Array]',
    int8Tag = '[object Int8Array]',
    int16Tag = '[object Int16Array]',
    int32Tag = '[object Int32Array]',
    uint8Tag = '[object Uint8Array]',
    uint8ClampedTag = '[object Uint8ClampedArray]',
    uint16Tag = '[object Uint16Array]',
    uint32Tag = '[object Uint32Array]'

  /** Used to identify `toStringTag` values of typed arrays. */
  var typedArrayTags = {}
  typedArrayTags[float32Tag] = typedArrayTags[float64Tag] = typedArrayTags[
    int8Tag
  ] = typedArrayTags[int16Tag] = typedArrayTags[int32Tag] = typedArrayTags[
    uint8Tag
  ] = typedArrayTags[uint8ClampedTag] = typedArrayTags[
    uint16Tag
  ] = typedArrayTags[uint32Tag] = true
  typedArrayTags[argsTag$1] = typedArrayTags[arrayTag] = typedArrayTags[
    arrayBufferTag
  ] = typedArrayTags[boolTag] = typedArrayTags[dataViewTag] = typedArrayTags[
    dateTag
  ] = typedArrayTags[errorTag] = typedArrayTags[funcTag$1] = typedArrayTags[
    mapTag
  ] = typedArrayTags[numberTag] = typedArrayTags[objectTag] = typedArrayTags[
    regexpTag
  ] = typedArrayTags[setTag] = typedArrayTags[stringTag] = typedArrayTags[
    weakMapTag
  ] = false

  /**
   * The base implementation of `_.isTypedArray` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
   */
  function baseIsTypedArray(value) {
    return (
      isObjectLike(value) &&
      isLength(value.length) &&
      !!typedArrayTags[baseGetTag(value)]
    )
  }

  /**
   * The base implementation of `_.unary` without support for storing metadata.
   *
   * @private
   * @param {Function} func The function to cap arguments for.
   * @returns {Function} Returns the new capped function.
   */
  function baseUnary(func) {
    return function(value) {
      return func(value)
    }
  }

  /** Detect free variable `exports`. */
  var freeExports$1 =
    typeof exports == 'object' && exports && !exports.nodeType && exports

  /** Detect free variable `module`. */
  var freeModule$1 =
    freeExports$1 &&
    typeof module == 'object' &&
    module &&
    !module.nodeType &&
    module

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports$1 = freeModule$1 && freeModule$1.exports === freeExports$1

  /** Detect free variable `process` from Node.js. */
  var freeProcess = moduleExports$1 && freeGlobal.process

  /** Used to access faster Node.js helpers. */
  var nodeUtil = (function() {
    try {
      // Use `util.types` for Node.js 10+.
      var types =
        freeModule$1 &&
        freeModule$1.require &&
        freeModule$1.require('util').types

      if (types) {
        return types
      }

      // Legacy `process.binding('util')` for Node.js < 10.
      return freeProcess && freeProcess.binding && freeProcess.binding('util')
    } catch (e) {}
  })()

  /* Node.js helper references. */
  var nodeIsTypedArray = nodeUtil && nodeUtil.isTypedArray

  /**
   * Checks if `value` is classified as a typed array.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a typed array, else `false`.
   * @example
   *
   * _.isTypedArray(new Uint8Array);
   * // => true
   *
   * _.isTypedArray([]);
   * // => false
   */
  var isTypedArray = nodeIsTypedArray
    ? baseUnary(nodeIsTypedArray)
    : baseIsTypedArray

  /** Used for built-in method references. */
  var objectProto$8 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$7 = objectProto$8.hasOwnProperty

  /**
   * Creates an array of the enumerable property names of the array-like `value`.
   *
   * @private
   * @param {*} value The value to query.
   * @param {boolean} inherited Specify returning inherited property names.
   * @returns {Array} Returns the array of property names.
   */
  function arrayLikeKeys(value, inherited) {
    var isArr = isArray(value),
      isArg = !isArr && isArguments(value),
      isBuff = !isArr && !isArg && isBuffer(value),
      isType = !isArr && !isArg && !isBuff && isTypedArray(value),
      skipIndexes = isArr || isArg || isBuff || isType,
      result = skipIndexes ? baseTimes(value.length, String) : [],
      length = result.length

    for (var key in value) {
      if (
        (inherited || hasOwnProperty$7.call(value, key)) &&
        !(
          skipIndexes &&
          // Safari 9 has enumerable `arguments.length` in strict mode.
          (key == 'length' ||
            // Node.js 0.10 has enumerable non-index properties on buffers.
            (isBuff && (key == 'offset' || key == 'parent')) ||
            // PhantomJS 2 has enumerable non-index properties on typed arrays.
            (isType &&
              (key == 'buffer' ||
                key == 'byteLength' ||
                key == 'byteOffset')) ||
            // Skip index properties.
            isIndex(key, length))
        )
      ) {
        result.push(key)
      }
    }
    return result
  }

  /**
   * Creates a unary function that invokes `func` with its argument transformed.
   *
   * @private
   * @param {Function} func The function to wrap.
   * @param {Function} transform The argument transform.
   * @returns {Function} Returns the new function.
   */
  function overArg(func, transform) {
    return function(arg) {
      return func(transform(arg))
    }
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeKeys = overArg(Object.keys, Object)

  /** Used for built-in method references. */
  var objectProto$9 = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$8 = objectProto$9.hasOwnProperty

  /**
   * The base implementation of `_.keys` which doesn't treat sparse arrays as dense.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   */
  function baseKeys(object) {
    if (!isPrototype(object)) {
      return nativeKeys(object)
    }
    var result = []
    for (var key in Object(object)) {
      if (hasOwnProperty$8.call(object, key) && key != 'constructor') {
        result.push(key)
      }
    }
    return result
  }

  /**
   * Creates an array of the own enumerable property names of `object`.
   *
   * **Note:** Non-object values are coerced to objects. See the
   * [ES spec](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
   * for more details.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.keys(new Foo);
   * // => ['a', 'b'] (iteration order is not guaranteed)
   *
   * _.keys('hi');
   * // => ['0', '1']
   */
  function keys(object) {
    return isArrayLike(object) ? arrayLikeKeys(object) : baseKeys(object)
  }

  /** Used for built-in method references. */
  var objectProto$a = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$9 = objectProto$a.hasOwnProperty

  /**
   * Assigns own enumerable string keyed properties of source objects to the
   * destination object. Source objects are applied from left to right.
   * Subsequent sources overwrite property assignments of previous sources.
   *
   * **Note:** This method mutates `object` and is loosely based on
   * [`Object.assign`](https://mdn.io/Object/assign).
   *
   * @static
   * @memberOf _
   * @since 0.10.0
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} [sources] The source objects.
   * @returns {Object} Returns `object`.
   * @see _.assignIn
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   * }
   *
   * function Bar() {
   *   this.c = 3;
   * }
   *
   * Foo.prototype.b = 2;
   * Bar.prototype.d = 4;
   *
   * _.assign({ 'a': 0 }, new Foo, new Bar);
   * // => { 'a': 1, 'c': 3 }
   */
  var assign = createAssigner(function(object, source) {
    if (isPrototype(source) || isArrayLike(source)) {
      copyObject(source, keys(source), object)
      return
    }
    for (var key in source) {
      if (hasOwnProperty$9.call(source, key)) {
        assignValue(object, key, source[key])
      }
    }
  })

  /**
   * This function is like
   * [`Object.keys`](http://ecma-international.org/ecma-262/7.0/#sec-object.keys)
   * except that it includes inherited enumerable properties.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   */
  function nativeKeysIn(object) {
    var result = []
    if (object != null) {
      for (var key in Object(object)) {
        result.push(key)
      }
    }
    return result
  }

  /** Used for built-in method references. */
  var objectProto$b = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$a = objectProto$b.hasOwnProperty

  /**
   * The base implementation of `_.keysIn` which doesn't treat sparse arrays as dense.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   */
  function baseKeysIn(object) {
    if (!isObject(object)) {
      return nativeKeysIn(object)
    }
    var isProto = isPrototype(object),
      result = []

    for (var key in object) {
      if (
        !(
          key == 'constructor' &&
          (isProto || !hasOwnProperty$a.call(object, key))
        )
      ) {
        result.push(key)
      }
    }
    return result
  }

  /**
   * Creates an array of the own and inherited enumerable property names of `object`.
   *
   * **Note:** Non-object values are coerced to objects.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.keysIn(new Foo);
   * // => ['a', 'b', 'c'] (iteration order is not guaranteed)
   */
  function keysIn$1(object) {
    return isArrayLike(object)
      ? arrayLikeKeys(object, true)
      : baseKeysIn(object)
  }

  /**
   * This method is like `_.assign` except that it iterates over own and
   * inherited source properties.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @alias extend
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} [sources] The source objects.
   * @returns {Object} Returns `object`.
   * @see _.assign
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   * }
   *
   * function Bar() {
   *   this.c = 3;
   * }
   *
   * Foo.prototype.b = 2;
   * Bar.prototype.d = 4;
   *
   * _.assignIn({ 'a': 0 }, new Foo, new Bar);
   * // => { 'a': 1, 'b': 2, 'c': 3, 'd': 4 }
   */
  var assignIn = createAssigner(function(object, source) {
    copyObject(source, keysIn$1(source), object)
  })

  /**
   * This method is like `_.assignIn` except that it accepts `customizer`
   * which is invoked to produce the assigned values. If `customizer` returns
   * `undefined`, assignment is handled by the method instead. The `customizer`
   * is invoked with five arguments: (objValue, srcValue, key, object, source).
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @alias extendWith
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} sources The source objects.
   * @param {Function} [customizer] The function to customize assigned values.
   * @returns {Object} Returns `object`.
   * @see _.assignWith
   * @example
   *
   * function customizer(objValue, srcValue) {
   *   return _.isUndefined(objValue) ? srcValue : objValue;
   * }
   *
   * var defaults = _.partialRight(_.assignInWith, customizer);
   *
   * defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
   * // => { 'a': 1, 'b': 2 }
   */
  var assignInWith = createAssigner(function(
    object,
    source,
    srcIndex,
    customizer
  ) {
    copyObject(source, keysIn$1(source), object, customizer)
  })

  /**
   * This method is like `_.assign` except that it accepts `customizer`
   * which is invoked to produce the assigned values. If `customizer` returns
   * `undefined`, assignment is handled by the method instead. The `customizer`
   * is invoked with five arguments: (objValue, srcValue, key, object, source).
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} sources The source objects.
   * @param {Function} [customizer] The function to customize assigned values.
   * @returns {Object} Returns `object`.
   * @see _.assignInWith
   * @example
   *
   * function customizer(objValue, srcValue) {
   *   return _.isUndefined(objValue) ? srcValue : objValue;
   * }
   *
   * var defaults = _.partialRight(_.assignWith, customizer);
   *
   * defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
   * // => { 'a': 1, 'b': 2 }
   */
  var assignWith = createAssigner(function(
    object,
    source,
    srcIndex,
    customizer
  ) {
    copyObject(source, keys(source), object, customizer)
  })

  /** Used to match property names within property paths. */
  var reIsDeepProp = /\.|\[(?:[^[\]]*|(["'])(?:(?!\1)[^\\]|\\.)*?\1)\]/,
    reIsPlainProp = /^\w*$/

  /**
   * Checks if `value` is a property name and not a property path.
   *
   * @private
   * @param {*} value The value to check.
   * @param {Object} [object] The object to query keys on.
   * @returns {boolean} Returns `true` if `value` is a property name, else `false`.
   */
  function isKey(value, object) {
    if (isArray(value)) {
      return false
    }
    var type = typeof value
    if (
      type == 'number' ||
      type == 'symbol' ||
      type == 'boolean' ||
      value == null ||
      isSymbol(value)
    ) {
      return true
    }
    return (
      reIsPlainProp.test(value) ||
      !reIsDeepProp.test(value) ||
      (object != null && value in Object(object))
    )
  }

  /* Built-in method references that are verified to be native. */
  var nativeCreate = getNative(Object, 'create')

  /**
   * Removes all key-value entries from the hash.
   *
   * @private
   * @name clear
   * @memberOf Hash
   */
  function hashClear() {
    this.__data__ = nativeCreate ? nativeCreate(null) : {}
    this.size = 0
  }

  /**
   * Removes `key` and its value from the hash.
   *
   * @private
   * @name delete
   * @memberOf Hash
   * @param {Object} hash The hash to modify.
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function hashDelete(key) {
    var result = this.has(key) && delete this.__data__[key]
    this.size -= result ? 1 : 0
    return result
  }

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED = '__lodash_hash_undefined__'

  /** Used for built-in method references. */
  var objectProto$c = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$b = objectProto$c.hasOwnProperty

  /**
   * Gets the hash value for `key`.
   *
   * @private
   * @name get
   * @memberOf Hash
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function hashGet(key) {
    var data = this.__data__
    if (nativeCreate) {
      var result = data[key]
      return result === HASH_UNDEFINED ? undefined : result
    }
    return hasOwnProperty$b.call(data, key) ? data[key] : undefined
  }

  /** Used for built-in method references. */
  var objectProto$d = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$c = objectProto$d.hasOwnProperty

  /**
   * Checks if a hash value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf Hash
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function hashHas(key) {
    var data = this.__data__
    return nativeCreate
      ? data[key] !== undefined
      : hasOwnProperty$c.call(data, key)
  }

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED$1 = '__lodash_hash_undefined__'

  /**
   * Sets the hash `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf Hash
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the hash instance.
   */
  function hashSet(key, value) {
    var data = this.__data__
    this.size += this.has(key) ? 0 : 1
    data[key] = nativeCreate && value === undefined ? HASH_UNDEFINED$1 : value
    return this
  }

  /**
   * Creates a hash object.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function Hash(entries) {
    var index = -1,
      length = entries == null ? 0 : entries.length

    this.clear()
    while (++index < length) {
      var entry = entries[index]
      this.set(entry[0], entry[1])
    }
  }

  // Add methods to `Hash`.
  Hash.prototype.clear = hashClear
  Hash.prototype['delete'] = hashDelete
  Hash.prototype.get = hashGet
  Hash.prototype.has = hashHas
  Hash.prototype.set = hashSet

  /**
   * Removes all key-value entries from the list cache.
   *
   * @private
   * @name clear
   * @memberOf ListCache
   */
  function listCacheClear() {
    this.__data__ = []
    this.size = 0
  }

  /**
   * Gets the index at which the `key` is found in `array` of key-value pairs.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} key The key to search for.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function assocIndexOf(array, key) {
    var length = array.length
    while (length--) {
      if (eq$1(array[length][0], key)) {
        return length
      }
    }
    return -1
  }

  /** Used for built-in method references. */
  var arrayProto = Array.prototype

  /** Built-in value references. */
  var splice = arrayProto.splice

  /**
   * Removes `key` and its value from the list cache.
   *
   * @private
   * @name delete
   * @memberOf ListCache
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function listCacheDelete(key) {
    var data = this.__data__,
      index = assocIndexOf(data, key)

    if (index < 0) {
      return false
    }
    var lastIndex = data.length - 1
    if (index == lastIndex) {
      data.pop()
    } else {
      splice.call(data, index, 1)
    }
    --this.size
    return true
  }

  /**
   * Gets the list cache value for `key`.
   *
   * @private
   * @name get
   * @memberOf ListCache
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function listCacheGet(key) {
    var data = this.__data__,
      index = assocIndexOf(data, key)

    return index < 0 ? undefined : data[index][1]
  }

  /**
   * Checks if a list cache value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf ListCache
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function listCacheHas(key) {
    return assocIndexOf(this.__data__, key) > -1
  }

  /**
   * Sets the list cache `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf ListCache
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the list cache instance.
   */
  function listCacheSet(key, value) {
    var data = this.__data__,
      index = assocIndexOf(data, key)

    if (index < 0) {
      ++this.size
      data.push([key, value])
    } else {
      data[index][1] = value
    }
    return this
  }

  /**
   * Creates an list cache object.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function ListCache(entries) {
    var index = -1,
      length = entries == null ? 0 : entries.length

    this.clear()
    while (++index < length) {
      var entry = entries[index]
      this.set(entry[0], entry[1])
    }
  }

  // Add methods to `ListCache`.
  ListCache.prototype.clear = listCacheClear
  ListCache.prototype['delete'] = listCacheDelete
  ListCache.prototype.get = listCacheGet
  ListCache.prototype.has = listCacheHas
  ListCache.prototype.set = listCacheSet

  /* Built-in method references that are verified to be native. */
  var Map$1 = getNative(root, 'Map')

  /**
   * Removes all key-value entries from the map.
   *
   * @private
   * @name clear
   * @memberOf MapCache
   */
  function mapCacheClear() {
    this.size = 0
    this.__data__ = {
      hash: new Hash(),
      map: new (Map$1 || ListCache)(),
      string: new Hash(),
    }
  }

  /**
   * Checks if `value` is suitable for use as unique object key.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is suitable, else `false`.
   */
  function isKeyable(value) {
    var type = typeof value
    return type == 'string' ||
      type == 'number' ||
      type == 'symbol' ||
      type == 'boolean'
      ? value !== '__proto__'
      : value === null
  }

  /**
   * Gets the data for `map`.
   *
   * @private
   * @param {Object} map The map to query.
   * @param {string} key The reference key.
   * @returns {*} Returns the map data.
   */
  function getMapData(map, key) {
    var data = map.__data__
    return isKeyable(key)
      ? data[typeof key == 'string' ? 'string' : 'hash']
      : data.map
  }

  /**
   * Removes `key` and its value from the map.
   *
   * @private
   * @name delete
   * @memberOf MapCache
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function mapCacheDelete(key) {
    var result = getMapData(this, key)['delete'](key)
    this.size -= result ? 1 : 0
    return result
  }

  /**
   * Gets the map value for `key`.
   *
   * @private
   * @name get
   * @memberOf MapCache
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function mapCacheGet(key) {
    return getMapData(this, key).get(key)
  }

  /**
   * Checks if a map value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf MapCache
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function mapCacheHas(key) {
    return getMapData(this, key).has(key)
  }

  /**
   * Sets the map `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf MapCache
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the map cache instance.
   */
  function mapCacheSet(key, value) {
    var data = getMapData(this, key),
      size = data.size

    data.set(key, value)
    this.size += data.size == size ? 0 : 1
    return this
  }

  /**
   * Creates a map cache object to store key-value pairs.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function MapCache(entries) {
    var index = -1,
      length = entries == null ? 0 : entries.length

    this.clear()
    while (++index < length) {
      var entry = entries[index]
      this.set(entry[0], entry[1])
    }
  }

  // Add methods to `MapCache`.
  MapCache.prototype.clear = mapCacheClear
  MapCache.prototype['delete'] = mapCacheDelete
  MapCache.prototype.get = mapCacheGet
  MapCache.prototype.has = mapCacheHas
  MapCache.prototype.set = mapCacheSet

  /** Error message constants. */
  var FUNC_ERROR_TEXT$2 = 'Expected a function'

  /**
   * Creates a function that memoizes the result of `func`. If `resolver` is
   * provided, it determines the cache key for storing the result based on the
   * arguments provided to the memoized function. By default, the first argument
   * provided to the memoized function is used as the map cache key. The `func`
   * is invoked with the `this` binding of the memoized function.
   *
   * **Note:** The cache is exposed as the `cache` property on the memoized
   * function. Its creation may be customized by replacing the `_.memoize.Cache`
   * constructor with one whose instances implement the
   * [`Map`](http://ecma-international.org/ecma-262/7.0/#sec-properties-of-the-map-prototype-object)
   * method interface of `clear`, `delete`, `get`, `has`, and `set`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to have its output memoized.
   * @param {Function} [resolver] The function to resolve the cache key.
   * @returns {Function} Returns the new memoized function.
   * @example
   *
   * var object = { 'a': 1, 'b': 2 };
   * var other = { 'c': 3, 'd': 4 };
   *
   * var values = _.memoize(_.values);
   * values(object);
   * // => [1, 2]
   *
   * values(other);
   * // => [3, 4]
   *
   * object.a = 2;
   * values(object);
   * // => [1, 2]
   *
   * // Modify the result cache.
   * values.cache.set(object, ['a', 'b']);
   * values(object);
   * // => ['a', 'b']
   *
   * // Replace `_.memoize.Cache`.
   * _.memoize.Cache = WeakMap;
   */
  function memoize(func, resolver) {
    if (
      typeof func != 'function' ||
      (resolver != null && typeof resolver != 'function')
    ) {
      throw new TypeError(FUNC_ERROR_TEXT$2)
    }
    var memoized = function() {
      var args = arguments,
        key = resolver ? resolver.apply(this, args) : args[0],
        cache = memoized.cache

      if (cache.has(key)) {
        return cache.get(key)
      }
      var result = func.apply(this, args)
      memoized.cache = cache.set(key, result) || cache
      return result
    }
    memoized.cache = new (memoize.Cache || MapCache)()
    return memoized
  }

  // Expose `MapCache`.
  memoize.Cache = MapCache

  /** Used as the maximum memoize cache size. */
  var MAX_MEMOIZE_SIZE = 500

  /**
   * A specialized version of `_.memoize` which clears the memoized function's
   * cache when it exceeds `MAX_MEMOIZE_SIZE`.
   *
   * @private
   * @param {Function} func The function to have its output memoized.
   * @returns {Function} Returns the new memoized function.
   */
  function memoizeCapped(func) {
    var result = memoize(func, function(key) {
      if (cache.size === MAX_MEMOIZE_SIZE) {
        cache.clear()
      }
      return key
    })

    var cache = result.cache
    return result
  }

  /** Used to match property names within property paths. */
  var rePropName = /[^.[\]]+|\[(?:(-?\d+(?:\.\d+)?)|(["'])((?:(?!\2)[^\\]|\\.)*?)\2)\]|(?=(?:\.|\[\])(?:\.|\[\]|$))/g

  /** Used to match backslashes in property paths. */
  var reEscapeChar = /\\(\\)?/g

  /**
   * Converts `string` to a property path array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the property path array.
   */
  var stringToPath = memoizeCapped(function(string) {
    var result = []
    if (string.charCodeAt(0) === 46 /* . */) {
      result.push('')
    }
    string.replace(rePropName, function(match, number, quote, subString) {
      result.push(
        quote ? subString.replace(reEscapeChar, '$1') : number || match
      )
    })
    return result
  })

  /**
   * Converts `value` to a string. An empty string is returned for `null`
   * and `undefined` values. The sign of `-0` is preserved.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {string} Returns the converted string.
   * @example
   *
   * _.toString(null);
   * // => ''
   *
   * _.toString(-0);
   * // => '-0'
   *
   * _.toString([1, 2, 3]);
   * // => '1,2,3'
   */
  function toString(value) {
    return value == null ? '' : baseToString(value)
  }

  /**
   * Casts `value` to a path array if it's not one.
   *
   * @private
   * @param {*} value The value to inspect.
   * @param {Object} [object] The object to query keys on.
   * @returns {Array} Returns the cast property path array.
   */
  function castPath(value, object) {
    if (isArray(value)) {
      return value
    }
    return isKey(value, object) ? [value] : stringToPath(toString(value))
  }

  /** Used as references for various `Number` constants. */
  var INFINITY$2 = 1 / 0

  /**
   * Converts `value` to a string key if it's not a string or symbol.
   *
   * @private
   * @param {*} value The value to inspect.
   * @returns {string|symbol} Returns the key.
   */
  function toKey(value) {
    if (typeof value == 'string' || isSymbol(value)) {
      return value
    }
    var result = value + ''
    return result == '0' && 1 / value == -INFINITY$2 ? '-0' : result
  }

  /**
   * The base implementation of `_.get` without support for default values.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the property to get.
   * @returns {*} Returns the resolved value.
   */
  function baseGet(object, path) {
    path = castPath(path, object)

    var index = 0,
      length = path.length

    while (object != null && index < length) {
      object = object[toKey(path[index++])]
    }
    return index && index == length ? object : undefined
  }

  /**
   * Gets the value at `path` of `object`. If the resolved value is
   * `undefined`, the `defaultValue` is returned in its place.
   *
   * @static
   * @memberOf _
   * @since 3.7.0
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the property to get.
   * @param {*} [defaultValue] The value returned for `undefined` resolved values.
   * @returns {*} Returns the resolved value.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 3 } }] };
   *
   * _.get(object, 'a[0].b.c');
   * // => 3
   *
   * _.get(object, ['a', '0', 'b', 'c']);
   * // => 3
   *
   * _.get(object, 'a.b.c', 'default');
   * // => 'default'
   */
  function get(object, path, defaultValue) {
    var result = object == null ? undefined : baseGet(object, path)
    return result === undefined ? defaultValue : result
  }

  /**
   * The base implementation of `_.at` without support for individual paths.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {string[]} paths The property paths to pick.
   * @returns {Array} Returns the picked elements.
   */
  function baseAt(object, paths) {
    var index = -1,
      length = paths.length,
      result = Array(length),
      skip = object == null

    while (++index < length) {
      result[index] = skip ? undefined : get(object, paths[index])
    }
    return result
  }

  /**
   * Appends the elements of `values` to `array`.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {Array} values The values to append.
   * @returns {Array} Returns `array`.
   */
  function arrayPush(array, values) {
    var index = -1,
      length = values.length,
      offset = array.length

    while (++index < length) {
      array[offset + index] = values[index]
    }
    return array
  }

  /** Built-in value references. */
  var spreadableSymbol = Symbol$1 ? Symbol$1.isConcatSpreadable : undefined

  /**
   * Checks if `value` is a flattenable `arguments` object or array.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is flattenable, else `false`.
   */
  function isFlattenable(value) {
    return (
      isArray(value) ||
      isArguments(value) ||
      !!(spreadableSymbol && value && value[spreadableSymbol])
    )
  }

  /**
   * The base implementation of `_.flatten` with support for restricting flattening.
   *
   * @private
   * @param {Array} array The array to flatten.
   * @param {number} depth The maximum recursion depth.
   * @param {boolean} [predicate=isFlattenable] The function invoked per iteration.
   * @param {boolean} [isStrict] Restrict to values that pass `predicate` checks.
   * @param {Array} [result=[]] The initial result value.
   * @returns {Array} Returns the new flattened array.
   */
  function baseFlatten(array, depth, predicate, isStrict, result) {
    var index = -1,
      length = array.length

    predicate || (predicate = isFlattenable)
    result || (result = [])

    while (++index < length) {
      var value = array[index]
      if (depth > 0 && predicate(value)) {
        if (depth > 1) {
          // Recursively flatten arrays (susceptible to call stack limits).
          baseFlatten(value, depth - 1, predicate, isStrict, result)
        } else {
          arrayPush(result, value)
        }
      } else if (!isStrict) {
        result[result.length] = value
      }
    }
    return result
  }

  /**
   * Flattens `array` a single level deep.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to flatten.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * _.flatten([1, [2, [3, [4]], 5]]);
   * // => [1, 2, [3, [4]], 5]
   */
  function flatten(array) {
    var length = array == null ? 0 : array.length
    return length ? baseFlatten(array, 1) : []
  }

  /**
   * A specialized version of `baseRest` which flattens the rest array.
   *
   * @private
   * @param {Function} func The function to apply a rest parameter to.
   * @returns {Function} Returns the new function.
   */
  function flatRest(func) {
    return setToString(overRest(func, undefined, flatten), func + '')
  }

  /**
   * Creates an array of values corresponding to `paths` of `object`.
   *
   * @static
   * @memberOf _
   * @since 1.0.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {...(string|string[])} [paths] The property paths to pick.
   * @returns {Array} Returns the picked values.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 3 } }, 4] };
   *
   * _.at(object, ['a[0].b.c', 'a[1]']);
   * // => [3, 4]
   */
  var at = flatRest(baseAt)

  /** Built-in value references. */
  var getPrototype = overArg(Object.getPrototypeOf, Object)

  /** `Object#toString` result references. */
  var objectTag$1 = '[object Object]'

  /** Used for built-in method references. */
  var funcProto$2 = Function.prototype,
    objectProto$e = Object.prototype

  /** Used to resolve the decompiled source of functions. */
  var funcToString$2 = funcProto$2.toString

  /** Used to check objects for own properties. */
  var hasOwnProperty$d = objectProto$e.hasOwnProperty

  /** Used to infer the `Object` constructor. */
  var objectCtorString = funcToString$2.call(Object)

  /**
   * Checks if `value` is a plain object, that is, an object created by the
   * `Object` constructor or one with a `[[Prototype]]` of `null`.
   *
   * @static
   * @memberOf _
   * @since 0.8.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a plain object, else `false`.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   * }
   *
   * _.isPlainObject(new Foo);
   * // => false
   *
   * _.isPlainObject([1, 2, 3]);
   * // => false
   *
   * _.isPlainObject({ 'x': 0, 'y': 0 });
   * // => true
   *
   * _.isPlainObject(Object.create(null));
   * // => true
   */
  function isPlainObject(value) {
    if (!isObjectLike(value) || baseGetTag(value) != objectTag$1) {
      return false
    }
    var proto = getPrototype(value)
    if (proto === null) {
      return true
    }
    var Ctor = hasOwnProperty$d.call(proto, 'constructor') && proto.constructor
    return (
      typeof Ctor == 'function' &&
      Ctor instanceof Ctor &&
      funcToString$2.call(Ctor) == objectCtorString
    )
  }

  /** `Object#toString` result references. */
  var domExcTag = '[object DOMException]',
    errorTag$1 = '[object Error]'

  /**
   * Checks if `value` is an `Error`, `EvalError`, `RangeError`, `ReferenceError`,
   * `SyntaxError`, `TypeError`, or `URIError` object.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an error object, else `false`.
   * @example
   *
   * _.isError(new Error);
   * // => true
   *
   * _.isError(Error);
   * // => false
   */
  function isError(value) {
    if (!isObjectLike(value)) {
      return false
    }
    var tag = baseGetTag(value)
    return (
      tag == errorTag$1 ||
      tag == domExcTag ||
      (typeof value.message == 'string' &&
        typeof value.name == 'string' &&
        !isPlainObject(value))
    )
  }

  /**
   * Attempts to invoke `func`, returning either the result or the caught error
   * object. Any additional arguments are provided to `func` when it's invoked.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Util
   * @param {Function} func The function to attempt.
   * @param {...*} [args] The arguments to invoke `func` with.
   * @returns {*} Returns the `func` result or error object.
   * @example
   *
   * // Avoid throwing errors for invalid selectors.
   * var elements = _.attempt(function(selector) {
   *   return document.querySelectorAll(selector);
   * }, '>_>');
   *
   * if (_.isError(elements)) {
   *   elements = [];
   * }
   */
  var attempt = baseRest(function(func, args) {
    try {
      return apply(func, undefined, args)
    } catch (e) {
      return isError(e) ? e : new Error(e)
    }
  })

  /** Error message constants. */
  var FUNC_ERROR_TEXT$3 = 'Expected a function'

  /**
   * Creates a function that invokes `func`, with the `this` binding and arguments
   * of the created function, while it's called less than `n` times. Subsequent
   * calls to the created function return the result of the last `func` invocation.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Function
   * @param {number} n The number of calls at which `func` is no longer invoked.
   * @param {Function} func The function to restrict.
   * @returns {Function} Returns the new restricted function.
   * @example
   *
   * jQuery(element).on('click', _.before(5, addContactToList));
   * // => Allows adding up to 4 contacts to the list.
   */
  function before(n, func) {
    var result
    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$3)
    }
    n = toInteger(n)
    return function() {
      if (--n > 0) {
        result = func.apply(this, arguments)
      }
      if (n <= 1) {
        func = undefined
      }
      return result
    }
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$7 = 1,
    WRAP_PARTIAL_FLAG$3 = 32

  /**
   * Creates a function that invokes `func` with the `this` binding of `thisArg`
   * and `partials` prepended to the arguments it receives.
   *
   * The `_.bind.placeholder` value, which defaults to `_` in monolithic builds,
   * may be used as a placeholder for partially applied arguments.
   *
   * **Note:** Unlike native `Function#bind`, this method doesn't set the "length"
   * property of bound functions.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to bind.
   * @param {*} thisArg The `this` binding of `func`.
   * @param {...*} [partials] The arguments to be partially applied.
   * @returns {Function} Returns the new bound function.
   * @example
   *
   * function greet(greeting, punctuation) {
   *   return greeting + ' ' + this.user + punctuation;
   * }
   *
   * var object = { 'user': 'fred' };
   *
   * var bound = _.bind(greet, object, 'hi');
   * bound('!');
   * // => 'hi fred!'
   *
   * // Bound with placeholders.
   * var bound = _.bind(greet, object, _, '!');
   * bound('hi');
   * // => 'hi fred!'
   */
  var bind = baseRest(function(func, thisArg, partials) {
    var bitmask = WRAP_BIND_FLAG$7
    if (partials.length) {
      var holders = replaceHolders(partials, getHolder(bind))
      bitmask |= WRAP_PARTIAL_FLAG$3
    }
    return createWrap(func, bitmask, thisArg, partials, holders)
  })

  // Assign default placeholders.
  bind.placeholder = {}

  /**
   * Binds methods of an object to the object itself, overwriting the existing
   * method.
   *
   * **Note:** This method doesn't set the "length" property of bound functions.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {Object} object The object to bind and assign the bound methods to.
   * @param {...(string|string[])} methodNames The object method names to bind.
   * @returns {Object} Returns `object`.
   * @example
   *
   * var view = {
   *   'label': 'docs',
   *   'click': function() {
   *     console.log('clicked ' + this.label);
   *   }
   * };
   *
   * _.bindAll(view, ['click']);
   * jQuery(element).on('click', view.click);
   * // => Logs 'clicked docs' when clicked.
   */
  var bindAll = flatRest(function(object, methodNames) {
    arrayEach(methodNames, function(key) {
      key = toKey(key)
      baseAssignValue(object, key, bind(object[key], object))
    })
    return object
  })

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_FLAG$8 = 1,
    WRAP_BIND_KEY_FLAG$5 = 2,
    WRAP_PARTIAL_FLAG$4 = 32

  /**
   * Creates a function that invokes the method at `object[key]` with `partials`
   * prepended to the arguments it receives.
   *
   * This method differs from `_.bind` by allowing bound functions to reference
   * methods that may be redefined or don't yet exist. See
   * [Peter Michaux's article](http://peter.michaux.ca/articles/lazy-function-definition-pattern)
   * for more details.
   *
   * The `_.bindKey.placeholder` value, which defaults to `_` in monolithic
   * builds, may be used as a placeholder for partially applied arguments.
   *
   * @static
   * @memberOf _
   * @since 0.10.0
   * @category Function
   * @param {Object} object The object to invoke the method on.
   * @param {string} key The key of the method.
   * @param {...*} [partials] The arguments to be partially applied.
   * @returns {Function} Returns the new bound function.
   * @example
   *
   * var object = {
   *   'user': 'fred',
   *   'greet': function(greeting, punctuation) {
   *     return greeting + ' ' + this.user + punctuation;
   *   }
   * };
   *
   * var bound = _.bindKey(object, 'greet', 'hi');
   * bound('!');
   * // => 'hi fred!'
   *
   * object.greet = function(greeting, punctuation) {
   *   return greeting + 'ya ' + this.user + punctuation;
   * };
   *
   * bound('!');
   * // => 'hiya fred!'
   *
   * // Bound with placeholders.
   * var bound = _.bindKey(object, 'greet', _, '!');
   * bound('hi');
   * // => 'hiya fred!'
   */
  var bindKey = baseRest(function(object, key, partials) {
    var bitmask = WRAP_BIND_FLAG$8 | WRAP_BIND_KEY_FLAG$5
    if (partials.length) {
      var holders = replaceHolders(partials, getHolder(bindKey))
      bitmask |= WRAP_PARTIAL_FLAG$4
    }
    return createWrap(key, bitmask, object, partials, holders)
  })

  // Assign default placeholders.
  bindKey.placeholder = {}

  /**
   * Casts `array` to a slice if it's needed.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {number} start The start position.
   * @param {number} [end=array.length] The end position.
   * @returns {Array} Returns the cast slice.
   */
  function castSlice(array, start, end) {
    var length = array.length
    end = end === undefined ? length : end
    return !start && end >= length ? array : baseSlice(array, start, end)
  }

  /** Used to compose unicode character classes. */
  var rsAstralRange = '\\ud800-\\udfff',
    rsComboMarksRange = '\\u0300-\\u036f',
    reComboHalfMarksRange = '\\ufe20-\\ufe2f',
    rsComboSymbolsRange = '\\u20d0-\\u20ff',
    rsComboRange =
      rsComboMarksRange + reComboHalfMarksRange + rsComboSymbolsRange,
    rsVarRange = '\\ufe0e\\ufe0f'

  /** Used to compose unicode capture groups. */
  var rsZWJ = '\\u200d'

  /** Used to detect strings with [zero-width joiners or code points from the astral planes](http://eev.ee/blog/2015/09/12/dark-corners-of-unicode/). */
  var reHasUnicode = RegExp(
    '[' + rsZWJ + rsAstralRange + rsComboRange + rsVarRange + ']'
  )

  /**
   * Checks if `string` contains Unicode symbols.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {boolean} Returns `true` if a symbol is found, else `false`.
   */
  function hasUnicode(string) {
    return reHasUnicode.test(string)
  }

  /**
   * Converts an ASCII `string` to an array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the converted array.
   */
  function asciiToArray(string) {
    return string.split('')
  }

  /** Used to compose unicode character classes. */
  var rsAstralRange$1 = '\\ud800-\\udfff',
    rsComboMarksRange$1 = '\\u0300-\\u036f',
    reComboHalfMarksRange$1 = '\\ufe20-\\ufe2f',
    rsComboSymbolsRange$1 = '\\u20d0-\\u20ff',
    rsComboRange$1 =
      rsComboMarksRange$1 + reComboHalfMarksRange$1 + rsComboSymbolsRange$1,
    rsVarRange$1 = '\\ufe0e\\ufe0f'

  /** Used to compose unicode capture groups. */
  var rsAstral = '[' + rsAstralRange$1 + ']',
    rsCombo = '[' + rsComboRange$1 + ']',
    rsFitz = '\\ud83c[\\udffb-\\udfff]',
    rsModifier = '(?:' + rsCombo + '|' + rsFitz + ')',
    rsNonAstral = '[^' + rsAstralRange$1 + ']',
    rsRegional = '(?:\\ud83c[\\udde6-\\uddff]){2}',
    rsSurrPair = '[\\ud800-\\udbff][\\udc00-\\udfff]',
    rsZWJ$1 = '\\u200d'

  /** Used to compose unicode regexes. */
  var reOptMod = rsModifier + '?',
    rsOptVar = '[' + rsVarRange$1 + ']?',
    rsOptJoin =
      '(?:' +
      rsZWJ$1 +
      '(?:' +
      [rsNonAstral, rsRegional, rsSurrPair].join('|') +
      ')' +
      rsOptVar +
      reOptMod +
      ')*',
    rsSeq = rsOptVar + reOptMod + rsOptJoin,
    rsSymbol =
      '(?:' +
      [
        rsNonAstral + rsCombo + '?',
        rsCombo,
        rsRegional,
        rsSurrPair,
        rsAstral,
      ].join('|') +
      ')'

  /** Used to match [string symbols](https://mathiasbynens.be/notes/javascript-unicode). */
  var reUnicode = RegExp(rsFitz + '(?=' + rsFitz + ')|' + rsSymbol + rsSeq, 'g')

  /**
   * Converts a Unicode `string` to an array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the converted array.
   */
  function unicodeToArray(string) {
    return string.match(reUnicode) || []
  }

  /**
   * Converts `string` to an array.
   *
   * @private
   * @param {string} string The string to convert.
   * @returns {Array} Returns the converted array.
   */
  function stringToArray(string) {
    return hasUnicode(string) ? unicodeToArray(string) : asciiToArray(string)
  }

  /**
   * Creates a function like `_.lowerFirst`.
   *
   * @private
   * @param {string} methodName The name of the `String` case method to use.
   * @returns {Function} Returns the new case function.
   */
  function createCaseFirst(methodName) {
    return function(string) {
      string = toString(string)

      var strSymbols = hasUnicode(string) ? stringToArray(string) : undefined

      var chr = strSymbols ? strSymbols[0] : string.charAt(0)

      var trailing = strSymbols
        ? castSlice(strSymbols, 1).join('')
        : string.slice(1)

      return chr[methodName]() + trailing
    }
  }

  /**
   * Converts the first character of `string` to upper case.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the converted string.
   * @example
   *
   * _.upperFirst('fred');
   * // => 'Fred'
   *
   * _.upperFirst('FRED');
   * // => 'FRED'
   */
  var upperFirst = createCaseFirst('toUpperCase')

  /**
   * Converts the first character of `string` to upper case and the remaining
   * to lower case.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to capitalize.
   * @returns {string} Returns the capitalized string.
   * @example
   *
   * _.capitalize('FRED');
   * // => 'Fred'
   */
  function capitalize(string) {
    return upperFirst(toString(string).toLowerCase())
  }

  /**
   * A specialized version of `_.reduce` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {*} [accumulator] The initial value.
   * @param {boolean} [initAccum] Specify using the first element of `array` as
   *  the initial value.
   * @returns {*} Returns the accumulated value.
   */
  function arrayReduce(array, iteratee, accumulator, initAccum) {
    var index = -1,
      length = array == null ? 0 : array.length

    if (initAccum && length) {
      accumulator = array[++index]
    }
    while (++index < length) {
      accumulator = iteratee(accumulator, array[index], index, array)
    }
    return accumulator
  }

  /**
   * The base implementation of `_.propertyOf` without support for deep paths.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Function} Returns the new accessor function.
   */
  function basePropertyOf(object) {
    return function(key) {
      return object == null ? undefined : object[key]
    }
  }

  /** Used to map Latin Unicode letters to basic Latin letters. */
  var deburredLetters = {
    // Latin-1 Supplement block.
    À: 'A',
    Á: 'A',
    Â: 'A',
    Ã: 'A',
    Ä: 'A',
    Å: 'A',
    à: 'a',
    á: 'a',
    â: 'a',
    ã: 'a',
    ä: 'a',
    å: 'a',
    Ç: 'C',
    ç: 'c',
    Ð: 'D',
    ð: 'd',
    È: 'E',
    É: 'E',
    Ê: 'E',
    Ë: 'E',
    è: 'e',
    é: 'e',
    ê: 'e',
    ë: 'e',
    Ì: 'I',
    Í: 'I',
    Î: 'I',
    Ï: 'I',
    ì: 'i',
    í: 'i',
    î: 'i',
    ï: 'i',
    Ñ: 'N',
    ñ: 'n',
    Ò: 'O',
    Ó: 'O',
    Ô: 'O',
    Õ: 'O',
    Ö: 'O',
    Ø: 'O',
    ò: 'o',
    ó: 'o',
    ô: 'o',
    õ: 'o',
    ö: 'o',
    ø: 'o',
    Ù: 'U',
    Ú: 'U',
    Û: 'U',
    Ü: 'U',
    ù: 'u',
    ú: 'u',
    û: 'u',
    ü: 'u',
    Ý: 'Y',
    ý: 'y',
    ÿ: 'y',
    Æ: 'Ae',
    æ: 'ae',
    Þ: 'Th',
    þ: 'th',
    ß: 'ss',
    // Latin Extended-A block.
    Ā: 'A',
    Ă: 'A',
    Ą: 'A',
    ā: 'a',
    ă: 'a',
    ą: 'a',
    Ć: 'C',
    Ĉ: 'C',
    Ċ: 'C',
    Č: 'C',
    ć: 'c',
    ĉ: 'c',
    ċ: 'c',
    č: 'c',
    Ď: 'D',
    Đ: 'D',
    ď: 'd',
    đ: 'd',
    Ē: 'E',
    Ĕ: 'E',
    Ė: 'E',
    Ę: 'E',
    Ě: 'E',
    ē: 'e',
    ĕ: 'e',
    ė: 'e',
    ę: 'e',
    ě: 'e',
    Ĝ: 'G',
    Ğ: 'G',
    Ġ: 'G',
    Ģ: 'G',
    ĝ: 'g',
    ğ: 'g',
    ġ: 'g',
    ģ: 'g',
    Ĥ: 'H',
    Ħ: 'H',
    ĥ: 'h',
    ħ: 'h',
    Ĩ: 'I',
    Ī: 'I',
    Ĭ: 'I',
    Į: 'I',
    İ: 'I',
    ĩ: 'i',
    ī: 'i',
    ĭ: 'i',
    į: 'i',
    ı: 'i',
    Ĵ: 'J',
    ĵ: 'j',
    Ķ: 'K',
    ķ: 'k',
    ĸ: 'k',
    Ĺ: 'L',
    Ļ: 'L',
    Ľ: 'L',
    Ŀ: 'L',
    Ł: 'L',
    ĺ: 'l',
    ļ: 'l',
    ľ: 'l',
    ŀ: 'l',
    ł: 'l',
    Ń: 'N',
    Ņ: 'N',
    Ň: 'N',
    Ŋ: 'N',
    ń: 'n',
    ņ: 'n',
    ň: 'n',
    ŋ: 'n',
    Ō: 'O',
    Ŏ: 'O',
    Ő: 'O',
    ō: 'o',
    ŏ: 'o',
    ő: 'o',
    Ŕ: 'R',
    Ŗ: 'R',
    Ř: 'R',
    ŕ: 'r',
    ŗ: 'r',
    ř: 'r',
    Ś: 'S',
    Ŝ: 'S',
    Ş: 'S',
    Š: 'S',
    ś: 's',
    ŝ: 's',
    ş: 's',
    š: 's',
    Ţ: 'T',
    Ť: 'T',
    Ŧ: 'T',
    ţ: 't',
    ť: 't',
    ŧ: 't',
    Ũ: 'U',
    Ū: 'U',
    Ŭ: 'U',
    Ů: 'U',
    Ű: 'U',
    Ų: 'U',
    ũ: 'u',
    ū: 'u',
    ŭ: 'u',
    ů: 'u',
    ű: 'u',
    ų: 'u',
    Ŵ: 'W',
    ŵ: 'w',
    Ŷ: 'Y',
    ŷ: 'y',
    Ÿ: 'Y',
    Ź: 'Z',
    Ż: 'Z',
    Ž: 'Z',
    ź: 'z',
    ż: 'z',
    ž: 'z',
    Ĳ: 'IJ',
    ĳ: 'ij',
    Œ: 'Oe',
    œ: 'oe',
    ŉ: "'n",
    ſ: 's',
  }

  /**
   * Used by `_.deburr` to convert Latin-1 Supplement and Latin Extended-A
   * letters to basic Latin letters.
   *
   * @private
   * @param {string} letter The matched letter to deburr.
   * @returns {string} Returns the deburred letter.
   */
  var deburrLetter = basePropertyOf(deburredLetters)

  /** Used to match Latin Unicode letters (excluding mathematical operators). */
  var reLatin = /[\xc0-\xd6\xd8-\xf6\xf8-\xff\u0100-\u017f]/g

  /** Used to compose unicode character classes. */
  var rsComboMarksRange$2 = '\\u0300-\\u036f',
    reComboHalfMarksRange$2 = '\\ufe20-\\ufe2f',
    rsComboSymbolsRange$2 = '\\u20d0-\\u20ff',
    rsComboRange$2 =
      rsComboMarksRange$2 + reComboHalfMarksRange$2 + rsComboSymbolsRange$2

  /** Used to compose unicode capture groups. */
  var rsCombo$1 = '[' + rsComboRange$2 + ']'

  /**
   * Used to match [combining diacritical marks](https://en.wikipedia.org/wiki/Combining_Diacritical_Marks) and
   * [combining diacritical marks for symbols](https://en.wikipedia.org/wiki/Combining_Diacritical_Marks_for_Symbols).
   */
  var reComboMark = RegExp(rsCombo$1, 'g')

  /**
   * Deburrs `string` by converting
   * [Latin-1 Supplement](https://en.wikipedia.org/wiki/Latin-1_Supplement_(Unicode_block)#Character_table)
   * and [Latin Extended-A](https://en.wikipedia.org/wiki/Latin_Extended-A)
   * letters to basic Latin letters and removing
   * [combining diacritical marks](https://en.wikipedia.org/wiki/Combining_Diacritical_Marks).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to deburr.
   * @returns {string} Returns the deburred string.
   * @example
   *
   * _.deburr('déjà vu');
   * // => 'deja vu'
   */
  function deburr(string) {
    string = toString(string)
    return (
      string && string.replace(reLatin, deburrLetter).replace(reComboMark, '')
    )
  }

  /** Used to match words composed of alphanumeric characters. */
  var reAsciiWord = /[^\x00-\x2f\x3a-\x40\x5b-\x60\x7b-\x7f]+/g

  /**
   * Splits an ASCII `string` into an array of its words.
   *
   * @private
   * @param {string} The string to inspect.
   * @returns {Array} Returns the words of `string`.
   */
  function asciiWords(string) {
    return string.match(reAsciiWord) || []
  }

  /** Used to detect strings that need a more robust regexp to match words. */
  var reHasUnicodeWord = /[a-z][A-Z]|[A-Z]{2}[a-z]|[0-9][a-zA-Z]|[a-zA-Z][0-9]|[^a-zA-Z0-9 ]/

  /**
   * Checks if `string` contains a word composed of Unicode symbols.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {boolean} Returns `true` if a word is found, else `false`.
   */
  function hasUnicodeWord(string) {
    return reHasUnicodeWord.test(string)
  }

  /** Used to compose unicode character classes. */
  var rsAstralRange$2 = '\\ud800-\\udfff',
    rsComboMarksRange$3 = '\\u0300-\\u036f',
    reComboHalfMarksRange$3 = '\\ufe20-\\ufe2f',
    rsComboSymbolsRange$3 = '\\u20d0-\\u20ff',
    rsComboRange$3 =
      rsComboMarksRange$3 + reComboHalfMarksRange$3 + rsComboSymbolsRange$3,
    rsDingbatRange = '\\u2700-\\u27bf',
    rsLowerRange = 'a-z\\xdf-\\xf6\\xf8-\\xff',
    rsMathOpRange = '\\xac\\xb1\\xd7\\xf7',
    rsNonCharRange = '\\x00-\\x2f\\x3a-\\x40\\x5b-\\x60\\x7b-\\xbf',
    rsPunctuationRange = '\\u2000-\\u206f',
    rsSpaceRange =
      ' \\t\\x0b\\f\\xa0\\ufeff\\n\\r\\u2028\\u2029\\u1680\\u180e\\u2000\\u2001\\u2002\\u2003\\u2004\\u2005\\u2006\\u2007\\u2008\\u2009\\u200a\\u202f\\u205f\\u3000',
    rsUpperRange = 'A-Z\\xc0-\\xd6\\xd8-\\xde',
    rsVarRange$2 = '\\ufe0e\\ufe0f',
    rsBreakRange =
      rsMathOpRange + rsNonCharRange + rsPunctuationRange + rsSpaceRange

  /** Used to compose unicode capture groups. */
  var rsApos = "['\u2019]",
    rsBreak = '[' + rsBreakRange + ']',
    rsCombo$2 = '[' + rsComboRange$3 + ']',
    rsDigits = '\\d+',
    rsDingbat = '[' + rsDingbatRange + ']',
    rsLower = '[' + rsLowerRange + ']',
    rsMisc =
      '[^' +
      rsAstralRange$2 +
      rsBreakRange +
      rsDigits +
      rsDingbatRange +
      rsLowerRange +
      rsUpperRange +
      ']',
    rsFitz$1 = '\\ud83c[\\udffb-\\udfff]',
    rsModifier$1 = '(?:' + rsCombo$2 + '|' + rsFitz$1 + ')',
    rsNonAstral$1 = '[^' + rsAstralRange$2 + ']',
    rsRegional$1 = '(?:\\ud83c[\\udde6-\\uddff]){2}',
    rsSurrPair$1 = '[\\ud800-\\udbff][\\udc00-\\udfff]',
    rsUpper = '[' + rsUpperRange + ']',
    rsZWJ$2 = '\\u200d'

  /** Used to compose unicode regexes. */
  var rsMiscLower = '(?:' + rsLower + '|' + rsMisc + ')',
    rsMiscUpper = '(?:' + rsUpper + '|' + rsMisc + ')',
    rsOptContrLower = '(?:' + rsApos + '(?:d|ll|m|re|s|t|ve))?',
    rsOptContrUpper = '(?:' + rsApos + '(?:D|LL|M|RE|S|T|VE))?',
    reOptMod$1 = rsModifier$1 + '?',
    rsOptVar$1 = '[' + rsVarRange$2 + ']?',
    rsOptJoin$1 =
      '(?:' +
      rsZWJ$2 +
      '(?:' +
      [rsNonAstral$1, rsRegional$1, rsSurrPair$1].join('|') +
      ')' +
      rsOptVar$1 +
      reOptMod$1 +
      ')*',
    rsOrdLower = '\\d*(?:1st|2nd|3rd|(?![123])\\dth)(?=\\b|[A-Z_])',
    rsOrdUpper = '\\d*(?:1ST|2ND|3RD|(?![123])\\dTH)(?=\\b|[a-z_])',
    rsSeq$1 = rsOptVar$1 + reOptMod$1 + rsOptJoin$1,
    rsEmoji =
      '(?:' + [rsDingbat, rsRegional$1, rsSurrPair$1].join('|') + ')' + rsSeq$1

  /** Used to match complex or compound words. */
  var reUnicodeWord = RegExp(
    [
      rsUpper +
        '?' +
        rsLower +
        '+' +
        rsOptContrLower +
        '(?=' +
        [rsBreak, rsUpper, '$'].join('|') +
        ')',
      rsMiscUpper +
        '+' +
        rsOptContrUpper +
        '(?=' +
        [rsBreak, rsUpper + rsMiscLower, '$'].join('|') +
        ')',
      rsUpper + '?' + rsMiscLower + '+' + rsOptContrLower,
      rsUpper + '+' + rsOptContrUpper,
      rsOrdUpper,
      rsOrdLower,
      rsDigits,
      rsEmoji,
    ].join('|'),
    'g'
  )

  /**
   * Splits a Unicode `string` into an array of its words.
   *
   * @private
   * @param {string} The string to inspect.
   * @returns {Array} Returns the words of `string`.
   */
  function unicodeWords(string) {
    return string.match(reUnicodeWord) || []
  }

  /**
   * Splits `string` into an array of its words.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to inspect.
   * @param {RegExp|string} [pattern] The pattern to match words.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the words of `string`.
   * @example
   *
   * _.words('fred, barney, & pebbles');
   * // => ['fred', 'barney', 'pebbles']
   *
   * _.words('fred, barney, & pebbles', /[^, ]+/g);
   * // => ['fred', 'barney', '&', 'pebbles']
   */
  function words(string, pattern, guard) {
    string = toString(string)
    pattern = guard ? undefined : pattern

    if (pattern === undefined) {
      return hasUnicodeWord(string) ? unicodeWords(string) : asciiWords(string)
    }
    return string.match(pattern) || []
  }

  /** Used to compose unicode capture groups. */
  var rsApos$1 = "['\u2019]"

  /** Used to match apostrophes. */
  var reApos = RegExp(rsApos$1, 'g')

  /**
   * Creates a function like `_.camelCase`.
   *
   * @private
   * @param {Function} callback The function to combine each word.
   * @returns {Function} Returns the new compounder function.
   */
  function createCompounder(callback) {
    return function(string) {
      return arrayReduce(
        words(deburr(string).replace(reApos, '')),
        callback,
        ''
      )
    }
  }

  /**
   * Converts `string` to [camel case](https://en.wikipedia.org/wiki/CamelCase).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the camel cased string.
   * @example
   *
   * _.camelCase('Foo Bar');
   * // => 'fooBar'
   *
   * _.camelCase('--foo-bar--');
   * // => 'fooBar'
   *
   * _.camelCase('__FOO_BAR__');
   * // => 'fooBar'
   */
  var camelCase = createCompounder(function(result, word, index) {
    word = word.toLowerCase()
    return result + (index ? capitalize(word) : word)
  })

  /**
   * Casts `value` as an array if it's not one.
   *
   * @static
   * @memberOf _
   * @since 4.4.0
   * @category Lang
   * @param {*} value The value to inspect.
   * @returns {Array} Returns the cast array.
   * @example
   *
   * _.castArray(1);
   * // => [1]
   *
   * _.castArray({ 'a': 1 });
   * // => [{ 'a': 1 }]
   *
   * _.castArray('abc');
   * // => ['abc']
   *
   * _.castArray(null);
   * // => [null]
   *
   * _.castArray(undefined);
   * // => [undefined]
   *
   * _.castArray();
   * // => []
   *
   * var array = [1, 2, 3];
   * console.log(_.castArray(array) === array);
   * // => true
   */
  function castArray() {
    if (!arguments.length) {
      return []
    }
    var value = arguments[0]
    return isArray(value) ? value : [value]
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeIsFinite = root.isFinite,
    nativeMin$2 = Math.min

  /**
   * Creates a function like `_.round`.
   *
   * @private
   * @param {string} methodName The name of the `Math` method to use when rounding.
   * @returns {Function} Returns the new round function.
   */
  function createRound(methodName) {
    var func = Math[methodName]
    return function(number, precision) {
      number = toNumber(number)
      precision = precision == null ? 0 : nativeMin$2(toInteger(precision), 292)
      if (precision && nativeIsFinite(number)) {
        // Shift with exponential notation to avoid floating-point issues.
        // See [MDN](https://mdn.io/round#Examples) for more details.
        var pair = (toString(number) + 'e').split('e'),
          value = func(pair[0] + 'e' + (+pair[1] + precision))

        pair = (toString(value) + 'e').split('e')
        return +(pair[0] + 'e' + (+pair[1] - precision))
      }
      return func(number)
    }
  }

  /**
   * Computes `number` rounded up to `precision`.
   *
   * @static
   * @memberOf _
   * @since 3.10.0
   * @category Math
   * @param {number} number The number to round up.
   * @param {number} [precision=0] The precision to round up to.
   * @returns {number} Returns the rounded up number.
   * @example
   *
   * _.ceil(4.006);
   * // => 5
   *
   * _.ceil(6.004, 2);
   * // => 6.01
   *
   * _.ceil(6040, -2);
   * // => 6100
   */
  var ceil$1 = createRound('ceil')

  /**
   * Creates a `lodash` wrapper instance that wraps `value` with explicit method
   * chain sequences enabled. The result of such sequences must be unwrapped
   * with `_#value`.
   *
   * @static
   * @memberOf _
   * @since 1.3.0
   * @category Seq
   * @param {*} value The value to wrap.
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'age': 36 },
   *   { 'user': 'fred',    'age': 40 },
   *   { 'user': 'pebbles', 'age': 1 }
   * ];
   *
   * var youngest = _
   *   .chain(users)
   *   .sortBy('age')
   *   .map(function(o) {
   *     return o.user + ' is ' + o.age;
   *   })
   *   .head()
   *   .value();
   * // => 'pebbles is 1'
   */
  function chain(value) {
    var result = lodash(value)
    result.__chain__ = true
    return result
  }

  /**
   * The base implementation of `_.clamp` which doesn't coerce arguments.
   *
   * @private
   * @param {number} number The number to clamp.
   * @param {number} [lower] The lower bound.
   * @param {number} upper The upper bound.
   * @returns {number} Returns the clamped number.
   */
  function baseClamp(number, lower, upper) {
    if (number === number) {
      if (upper !== undefined) {
        number = number <= upper ? number : upper
      }
      if (lower !== undefined) {
        number = number >= lower ? number : lower
      }
    }
    return number
  }

  /**
   * Clamps `number` within the inclusive `lower` and `upper` bounds.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Number
   * @param {number} number The number to clamp.
   * @param {number} [lower] The lower bound.
   * @param {number} upper The upper bound.
   * @returns {number} Returns the clamped number.
   * @example
   *
   * _.clamp(-10, -5, 5);
   * // => -5
   *
   * _.clamp(10, -5, 5);
   * // => 5
   */
  function clamp(number, lower, upper) {
    if (upper === undefined) {
      upper = lower
      lower = undefined
    }
    if (upper !== undefined) {
      upper = toNumber(upper)
      upper = upper === upper ? upper : 0
    }
    if (lower !== undefined) {
      lower = toNumber(lower)
      lower = lower === lower ? lower : 0
    }
    return baseClamp(toNumber(number), lower, upper)
  }

  /**
   * Removes all key-value entries from the stack.
   *
   * @private
   * @name clear
   * @memberOf Stack
   */
  function stackClear() {
    this.__data__ = new ListCache()
    this.size = 0
  }

  /**
   * Removes `key` and its value from the stack.
   *
   * @private
   * @name delete
   * @memberOf Stack
   * @param {string} key The key of the value to remove.
   * @returns {boolean} Returns `true` if the entry was removed, else `false`.
   */
  function stackDelete(key) {
    var data = this.__data__,
      result = data['delete'](key)

    this.size = data.size
    return result
  }

  /**
   * Gets the stack value for `key`.
   *
   * @private
   * @name get
   * @memberOf Stack
   * @param {string} key The key of the value to get.
   * @returns {*} Returns the entry value.
   */
  function stackGet(key) {
    return this.__data__.get(key)
  }

  /**
   * Checks if a stack value for `key` exists.
   *
   * @private
   * @name has
   * @memberOf Stack
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function stackHas(key) {
    return this.__data__.has(key)
  }

  /** Used as the size to enable large array optimizations. */
  var LARGE_ARRAY_SIZE = 200

  /**
   * Sets the stack `key` to `value`.
   *
   * @private
   * @name set
   * @memberOf Stack
   * @param {string} key The key of the value to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns the stack cache instance.
   */
  function stackSet(key, value) {
    var data = this.__data__
    if (data instanceof ListCache) {
      var pairs = data.__data__
      if (!Map$1 || pairs.length < LARGE_ARRAY_SIZE - 1) {
        pairs.push([key, value])
        this.size = ++data.size
        return this
      }
      data = this.__data__ = new MapCache(pairs)
    }
    data.set(key, value)
    this.size = data.size
    return this
  }

  /**
   * Creates a stack cache object to store key-value pairs.
   *
   * @private
   * @constructor
   * @param {Array} [entries] The key-value pairs to cache.
   */
  function Stack(entries) {
    var data = (this.__data__ = new ListCache(entries))
    this.size = data.size
  }

  // Add methods to `Stack`.
  Stack.prototype.clear = stackClear
  Stack.prototype['delete'] = stackDelete
  Stack.prototype.get = stackGet
  Stack.prototype.has = stackHas
  Stack.prototype.set = stackSet

  /**
   * The base implementation of `_.assign` without support for multiple sources
   * or `customizer` functions.
   *
   * @private
   * @param {Object} object The destination object.
   * @param {Object} source The source object.
   * @returns {Object} Returns `object`.
   */
  function baseAssign(object, source) {
    return object && copyObject(source, keys(source), object)
  }

  /**
   * The base implementation of `_.assignIn` without support for multiple sources
   * or `customizer` functions.
   *
   * @private
   * @param {Object} object The destination object.
   * @param {Object} source The source object.
   * @returns {Object} Returns `object`.
   */
  function baseAssignIn(object, source) {
    return object && copyObject(source, keysIn$1(source), object)
  }

  /** Detect free variable `exports`. */
  var freeExports$2 =
    typeof exports == 'object' && exports && !exports.nodeType && exports

  /** Detect free variable `module`. */
  var freeModule$2 =
    freeExports$2 &&
    typeof module == 'object' &&
    module &&
    !module.nodeType &&
    module

  /** Detect the popular CommonJS extension `module.exports`. */
  var moduleExports$2 = freeModule$2 && freeModule$2.exports === freeExports$2

  /** Built-in value references. */
  var Buffer$1 = moduleExports$2 ? root.Buffer : undefined,
    allocUnsafe = Buffer$1 ? Buffer$1.allocUnsafe : undefined

  /**
   * Creates a clone of  `buffer`.
   *
   * @private
   * @param {Buffer} buffer The buffer to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Buffer} Returns the cloned buffer.
   */
  function cloneBuffer(buffer, isDeep) {
    if (isDeep) {
      return buffer.slice()
    }
    var length = buffer.length,
      result = allocUnsafe
        ? allocUnsafe(length)
        : new buffer.constructor(length)

    buffer.copy(result)
    return result
  }

  /**
   * A specialized version of `_.filter` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {Array} Returns the new filtered array.
   */
  function arrayFilter(array, predicate) {
    var index = -1,
      length = array == null ? 0 : array.length,
      resIndex = 0,
      result = []

    while (++index < length) {
      var value = array[index]
      if (predicate(value, index, array)) {
        result[resIndex++] = value
      }
    }
    return result
  }

  /**
   * This method returns a new empty array.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {Array} Returns the new empty array.
   * @example
   *
   * var arrays = _.times(2, _.stubArray);
   *
   * console.log(arrays);
   * // => [[], []]
   *
   * console.log(arrays[0] === arrays[1]);
   * // => false
   */
  function stubArray() {
    return []
  }

  /** Used for built-in method references. */
  var objectProto$f = Object.prototype

  /** Built-in value references. */
  var propertyIsEnumerable$1 = objectProto$f.propertyIsEnumerable

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeGetSymbols = Object.getOwnPropertySymbols

  /**
   * Creates an array of the own enumerable symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of symbols.
   */
  var getSymbols = !nativeGetSymbols
    ? stubArray
    : function(object) {
        if (object == null) {
          return []
        }
        object = Object(object)
        return arrayFilter(nativeGetSymbols(object), function(symbol) {
          return propertyIsEnumerable$1.call(object, symbol)
        })
      }

  /**
   * Copies own symbols of `source` to `object`.
   *
   * @private
   * @param {Object} source The object to copy symbols from.
   * @param {Object} [object={}] The object to copy symbols to.
   * @returns {Object} Returns `object`.
   */
  function copySymbols(source, object) {
    return copyObject(source, getSymbols(source), object)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeGetSymbols$1 = Object.getOwnPropertySymbols

  /**
   * Creates an array of the own and inherited enumerable symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of symbols.
   */
  var getSymbolsIn = !nativeGetSymbols$1
    ? stubArray
    : function(object) {
        var result = []
        while (object) {
          arrayPush(result, getSymbols(object))
          object = getPrototype(object)
        }
        return result
      }

  /**
   * Copies own and inherited symbols of `source` to `object`.
   *
   * @private
   * @param {Object} source The object to copy symbols from.
   * @param {Object} [object={}] The object to copy symbols to.
   * @returns {Object} Returns `object`.
   */
  function copySymbolsIn(source, object) {
    return copyObject(source, getSymbolsIn(source), object)
  }

  /**
   * The base implementation of `getAllKeys` and `getAllKeysIn` which uses
   * `keysFunc` and `symbolsFunc` to get the enumerable property names and
   * symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Function} keysFunc The function to get the keys of `object`.
   * @param {Function} symbolsFunc The function to get the symbols of `object`.
   * @returns {Array} Returns the array of property names and symbols.
   */
  function baseGetAllKeys(object, keysFunc, symbolsFunc) {
    var result = keysFunc(object)
    return isArray(object) ? result : arrayPush(result, symbolsFunc(object))
  }

  /**
   * Creates an array of own enumerable property names and symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names and symbols.
   */
  function getAllKeys(object) {
    return baseGetAllKeys(object, keys, getSymbols)
  }

  /**
   * Creates an array of own and inherited enumerable property names and
   * symbols of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property names and symbols.
   */
  function getAllKeysIn(object) {
    return baseGetAllKeys(object, keysIn$1, getSymbolsIn)
  }

  /* Built-in method references that are verified to be native. */
  var DataView = getNative(root, 'DataView')

  /* Built-in method references that are verified to be native. */
  var Promise = getNative(root, 'Promise')

  /* Built-in method references that are verified to be native. */
  var Set = getNative(root, 'Set')

  /** `Object#toString` result references. */
  var mapTag$1 = '[object Map]',
    objectTag$2 = '[object Object]',
    promiseTag = '[object Promise]',
    setTag$1 = '[object Set]',
    weakMapTag$1 = '[object WeakMap]'

  var dataViewTag$1 = '[object DataView]'

  /** Used to detect maps, sets, and weakmaps. */
  var dataViewCtorString = toSource(DataView),
    mapCtorString = toSource(Map$1),
    promiseCtorString = toSource(Promise),
    setCtorString = toSource(Set),
    weakMapCtorString = toSource(WeakMap)

  /**
   * Gets the `toStringTag` of `value`.
   *
   * @private
   * @param {*} value The value to query.
   * @returns {string} Returns the `toStringTag`.
   */
  var getTag = baseGetTag

  // Fallback for data views, maps, sets, and weak maps in IE 11 and promises in Node.js < 6.
  if (
    (DataView && getTag(new DataView(new ArrayBuffer(1))) != dataViewTag$1) ||
    (Map$1 && getTag(new Map$1()) != mapTag$1) ||
    (Promise && getTag(Promise.resolve()) != promiseTag) ||
    (Set && getTag(new Set()) != setTag$1) ||
    (WeakMap && getTag(new WeakMap()) != weakMapTag$1)
  ) {
    getTag = function(value) {
      var result = baseGetTag(value),
        Ctor = result == objectTag$2 ? value.constructor : undefined,
        ctorString = Ctor ? toSource(Ctor) : ''

      if (ctorString) {
        switch (ctorString) {
          case dataViewCtorString:
            return dataViewTag$1
          case mapCtorString:
            return mapTag$1
          case promiseCtorString:
            return promiseTag
          case setCtorString:
            return setTag$1
          case weakMapCtorString:
            return weakMapTag$1
        }
      }
      return result
    }
  }

  var getTag$1 = getTag

  /** Used for built-in method references. */
  var objectProto$g = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$e = objectProto$g.hasOwnProperty

  /**
   * Initializes an array clone.
   *
   * @private
   * @param {Array} array The array to clone.
   * @returns {Array} Returns the initialized clone.
   */
  function initCloneArray(array) {
    var length = array.length,
      result = new array.constructor(length)

    // Add properties assigned by `RegExp#exec`.
    if (
      length &&
      typeof array[0] == 'string' &&
      hasOwnProperty$e.call(array, 'index')
    ) {
      result.index = array.index
      result.input = array.input
    }
    return result
  }

  /** Built-in value references. */
  var Uint8Array = root.Uint8Array

  /**
   * Creates a clone of `arrayBuffer`.
   *
   * @private
   * @param {ArrayBuffer} arrayBuffer The array buffer to clone.
   * @returns {ArrayBuffer} Returns the cloned array buffer.
   */
  function cloneArrayBuffer(arrayBuffer) {
    var result = new arrayBuffer.constructor(arrayBuffer.byteLength)
    new Uint8Array(result).set(new Uint8Array(arrayBuffer))
    return result
  }

  /**
   * Creates a clone of `dataView`.
   *
   * @private
   * @param {Object} dataView The data view to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Object} Returns the cloned data view.
   */
  function cloneDataView(dataView, isDeep) {
    var buffer = isDeep ? cloneArrayBuffer(dataView.buffer) : dataView.buffer
    return new dataView.constructor(
      buffer,
      dataView.byteOffset,
      dataView.byteLength
    )
  }

  /** Used to match `RegExp` flags from their coerced string values. */
  var reFlags = /\w*$/

  /**
   * Creates a clone of `regexp`.
   *
   * @private
   * @param {Object} regexp The regexp to clone.
   * @returns {Object} Returns the cloned regexp.
   */
  function cloneRegExp(regexp) {
    var result = new regexp.constructor(regexp.source, reFlags.exec(regexp))
    result.lastIndex = regexp.lastIndex
    return result
  }

  /** Used to convert symbols to primitives and strings. */
  var symbolProto$1 = Symbol$1 ? Symbol$1.prototype : undefined,
    symbolValueOf = symbolProto$1 ? symbolProto$1.valueOf : undefined

  /**
   * Creates a clone of the `symbol` object.
   *
   * @private
   * @param {Object} symbol The symbol object to clone.
   * @returns {Object} Returns the cloned symbol object.
   */
  function cloneSymbol(symbol) {
    return symbolValueOf ? Object(symbolValueOf.call(symbol)) : {}
  }

  /**
   * Creates a clone of `typedArray`.
   *
   * @private
   * @param {Object} typedArray The typed array to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Object} Returns the cloned typed array.
   */
  function cloneTypedArray(typedArray, isDeep) {
    var buffer = isDeep
      ? cloneArrayBuffer(typedArray.buffer)
      : typedArray.buffer
    return new typedArray.constructor(
      buffer,
      typedArray.byteOffset,
      typedArray.length
    )
  }

  /** `Object#toString` result references. */
  var boolTag$1 = '[object Boolean]',
    dateTag$1 = '[object Date]',
    mapTag$2 = '[object Map]',
    numberTag$1 = '[object Number]',
    regexpTag$1 = '[object RegExp]',
    setTag$2 = '[object Set]',
    stringTag$1 = '[object String]',
    symbolTag$1 = '[object Symbol]'

  var arrayBufferTag$1 = '[object ArrayBuffer]',
    dataViewTag$2 = '[object DataView]',
    float32Tag$1 = '[object Float32Array]',
    float64Tag$1 = '[object Float64Array]',
    int8Tag$1 = '[object Int8Array]',
    int16Tag$1 = '[object Int16Array]',
    int32Tag$1 = '[object Int32Array]',
    uint8Tag$1 = '[object Uint8Array]',
    uint8ClampedTag$1 = '[object Uint8ClampedArray]',
    uint16Tag$1 = '[object Uint16Array]',
    uint32Tag$1 = '[object Uint32Array]'

  /**
   * Initializes an object clone based on its `toStringTag`.
   *
   * **Note:** This function only supports cloning values with tags of
   * `Boolean`, `Date`, `Error`, `Map`, `Number`, `RegExp`, `Set`, or `String`.
   *
   * @private
   * @param {Object} object The object to clone.
   * @param {string} tag The `toStringTag` of the object to clone.
   * @param {boolean} [isDeep] Specify a deep clone.
   * @returns {Object} Returns the initialized clone.
   */
  function initCloneByTag(object, tag, isDeep) {
    var Ctor = object.constructor
    switch (tag) {
      case arrayBufferTag$1:
        return cloneArrayBuffer(object)

      case boolTag$1:
      case dateTag$1:
        return new Ctor(+object)

      case dataViewTag$2:
        return cloneDataView(object, isDeep)

      case float32Tag$1:
      case float64Tag$1:
      case int8Tag$1:
      case int16Tag$1:
      case int32Tag$1:
      case uint8Tag$1:
      case uint8ClampedTag$1:
      case uint16Tag$1:
      case uint32Tag$1:
        return cloneTypedArray(object, isDeep)

      case mapTag$2:
        return new Ctor()

      case numberTag$1:
      case stringTag$1:
        return new Ctor(object)

      case regexpTag$1:
        return cloneRegExp(object)

      case setTag$2:
        return new Ctor()

      case symbolTag$1:
        return cloneSymbol(object)
    }
  }

  /**
   * Initializes an object clone.
   *
   * @private
   * @param {Object} object The object to clone.
   * @returns {Object} Returns the initialized clone.
   */
  function initCloneObject(object) {
    return typeof object.constructor == 'function' && !isPrototype(object)
      ? baseCreate(getPrototype(object))
      : {}
  }

  /** `Object#toString` result references. */
  var mapTag$3 = '[object Map]'

  /**
   * The base implementation of `_.isMap` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a map, else `false`.
   */
  function baseIsMap(value) {
    return isObjectLike(value) && getTag$1(value) == mapTag$3
  }

  /* Node.js helper references. */
  var nodeIsMap = nodeUtil && nodeUtil.isMap

  /**
   * Checks if `value` is classified as a `Map` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a map, else `false`.
   * @example
   *
   * _.isMap(new Map);
   * // => true
   *
   * _.isMap(new WeakMap);
   * // => false
   */
  var isMap = nodeIsMap ? baseUnary(nodeIsMap) : baseIsMap

  /** `Object#toString` result references. */
  var setTag$3 = '[object Set]'

  /**
   * The base implementation of `_.isSet` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a set, else `false`.
   */
  function baseIsSet(value) {
    return isObjectLike(value) && getTag$1(value) == setTag$3
  }

  /* Node.js helper references. */
  var nodeIsSet = nodeUtil && nodeUtil.isSet

  /**
   * Checks if `value` is classified as a `Set` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a set, else `false`.
   * @example
   *
   * _.isSet(new Set);
   * // => true
   *
   * _.isSet(new WeakSet);
   * // => false
   */
  var isSet = nodeIsSet ? baseUnary(nodeIsSet) : baseIsSet

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG = 1,
    CLONE_FLAT_FLAG = 2,
    CLONE_SYMBOLS_FLAG = 4

  /** `Object#toString` result references. */
  var argsTag$2 = '[object Arguments]',
    arrayTag$1 = '[object Array]',
    boolTag$2 = '[object Boolean]',
    dateTag$2 = '[object Date]',
    errorTag$2 = '[object Error]',
    funcTag$2 = '[object Function]',
    genTag$1 = '[object GeneratorFunction]',
    mapTag$4 = '[object Map]',
    numberTag$2 = '[object Number]',
    objectTag$3 = '[object Object]',
    regexpTag$2 = '[object RegExp]',
    setTag$4 = '[object Set]',
    stringTag$2 = '[object String]',
    symbolTag$2 = '[object Symbol]',
    weakMapTag$2 = '[object WeakMap]'

  var arrayBufferTag$2 = '[object ArrayBuffer]',
    dataViewTag$3 = '[object DataView]',
    float32Tag$2 = '[object Float32Array]',
    float64Tag$2 = '[object Float64Array]',
    int8Tag$2 = '[object Int8Array]',
    int16Tag$2 = '[object Int16Array]',
    int32Tag$2 = '[object Int32Array]',
    uint8Tag$2 = '[object Uint8Array]',
    uint8ClampedTag$2 = '[object Uint8ClampedArray]',
    uint16Tag$2 = '[object Uint16Array]',
    uint32Tag$2 = '[object Uint32Array]'

  /** Used to identify `toStringTag` values supported by `_.clone`. */
  var cloneableTags = {}
  cloneableTags[argsTag$2] = cloneableTags[arrayTag$1] = cloneableTags[
    arrayBufferTag$2
  ] = cloneableTags[dataViewTag$3] = cloneableTags[boolTag$2] = cloneableTags[
    dateTag$2
  ] = cloneableTags[float32Tag$2] = cloneableTags[float64Tag$2] = cloneableTags[
    int8Tag$2
  ] = cloneableTags[int16Tag$2] = cloneableTags[int32Tag$2] = cloneableTags[
    mapTag$4
  ] = cloneableTags[numberTag$2] = cloneableTags[objectTag$3] = cloneableTags[
    regexpTag$2
  ] = cloneableTags[setTag$4] = cloneableTags[stringTag$2] = cloneableTags[
    symbolTag$2
  ] = cloneableTags[uint8Tag$2] = cloneableTags[
    uint8ClampedTag$2
  ] = cloneableTags[uint16Tag$2] = cloneableTags[uint32Tag$2] = true
  cloneableTags[errorTag$2] = cloneableTags[funcTag$2] = cloneableTags[
    weakMapTag$2
  ] = false

  /**
   * The base implementation of `_.clone` and `_.cloneDeep` which tracks
   * traversed objects.
   *
   * @private
   * @param {*} value The value to clone.
   * @param {boolean} bitmask The bitmask flags.
   *  1 - Deep clone
   *  2 - Flatten inherited properties
   *  4 - Clone symbols
   * @param {Function} [customizer] The function to customize cloning.
   * @param {string} [key] The key of `value`.
   * @param {Object} [object] The parent object of `value`.
   * @param {Object} [stack] Tracks traversed objects and their clone counterparts.
   * @returns {*} Returns the cloned value.
   */
  function baseClone(value, bitmask, customizer, key, object, stack) {
    var result,
      isDeep = bitmask & CLONE_DEEP_FLAG,
      isFlat = bitmask & CLONE_FLAT_FLAG,
      isFull = bitmask & CLONE_SYMBOLS_FLAG

    if (customizer) {
      result = object
        ? customizer(value, key, object, stack)
        : customizer(value)
    }
    if (result !== undefined) {
      return result
    }
    if (!isObject(value)) {
      return value
    }
    var isArr = isArray(value)
    if (isArr) {
      result = initCloneArray(value)
      if (!isDeep) {
        return copyArray(value, result)
      }
    } else {
      var tag = getTag$1(value),
        isFunc = tag == funcTag$2 || tag == genTag$1

      if (isBuffer(value)) {
        return cloneBuffer(value, isDeep)
      }
      if (tag == objectTag$3 || tag == argsTag$2 || (isFunc && !object)) {
        result = isFlat || isFunc ? {} : initCloneObject(value)
        if (!isDeep) {
          return isFlat
            ? copySymbolsIn(value, baseAssignIn(result, value))
            : copySymbols(value, baseAssign(result, value))
        }
      } else {
        if (!cloneableTags[tag]) {
          return object ? value : {}
        }
        result = initCloneByTag(value, tag, isDeep)
      }
    }
    // Check for circular references and return its corresponding clone.
    stack || (stack = new Stack())
    var stacked = stack.get(value)
    if (stacked) {
      return stacked
    }
    stack.set(value, result)

    if (isSet(value)) {
      value.forEach(function(subValue) {
        result.add(
          baseClone(subValue, bitmask, customizer, subValue, value, stack)
        )
      })
    } else if (isMap(value)) {
      value.forEach(function(subValue, key) {
        result.set(
          key,
          baseClone(subValue, bitmask, customizer, key, value, stack)
        )
      })
    }

    var keysFunc = isFull
      ? isFlat
        ? getAllKeysIn
        : getAllKeys
      : isFlat
      ? keysIn
      : keys

    var props = isArr ? undefined : keysFunc(value)
    arrayEach(props || value, function(subValue, key) {
      if (props) {
        key = subValue
        subValue = value[key]
      }
      // Recursively populate clone (susceptible to call stack limits).
      assignValue(
        result,
        key,
        baseClone(subValue, bitmask, customizer, key, value, stack)
      )
    })
    return result
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_SYMBOLS_FLAG$1 = 4

  /**
   * Creates a shallow clone of `value`.
   *
   * **Note:** This method is loosely based on the
   * [structured clone algorithm](https://mdn.io/Structured_clone_algorithm)
   * and supports cloning arrays, array buffers, booleans, date objects, maps,
   * numbers, `Object` objects, regexes, sets, strings, symbols, and typed
   * arrays. The own enumerable properties of `arguments` objects are cloned
   * as plain objects. An empty object is returned for uncloneable values such
   * as error objects, functions, DOM nodes, and WeakMaps.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to clone.
   * @returns {*} Returns the cloned value.
   * @see _.cloneDeep
   * @example
   *
   * var objects = [{ 'a': 1 }, { 'b': 2 }];
   *
   * var shallow = _.clone(objects);
   * console.log(shallow[0] === objects[0]);
   * // => true
   */
  function clone(value) {
    return baseClone(value, CLONE_SYMBOLS_FLAG$1)
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$1 = 1,
    CLONE_SYMBOLS_FLAG$2 = 4

  /**
   * This method is like `_.clone` except that it recursively clones `value`.
   *
   * @static
   * @memberOf _
   * @since 1.0.0
   * @category Lang
   * @param {*} value The value to recursively clone.
   * @returns {*} Returns the deep cloned value.
   * @see _.clone
   * @example
   *
   * var objects = [{ 'a': 1 }, { 'b': 2 }];
   *
   * var deep = _.cloneDeep(objects);
   * console.log(deep[0] === objects[0]);
   * // => false
   */
  function cloneDeep(value) {
    return baseClone(value, CLONE_DEEP_FLAG$1 | CLONE_SYMBOLS_FLAG$2)
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$2 = 1,
    CLONE_SYMBOLS_FLAG$3 = 4

  /**
   * This method is like `_.cloneWith` except that it recursively clones `value`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to recursively clone.
   * @param {Function} [customizer] The function to customize cloning.
   * @returns {*} Returns the deep cloned value.
   * @see _.cloneWith
   * @example
   *
   * function customizer(value) {
   *   if (_.isElement(value)) {
   *     return value.cloneNode(true);
   *   }
   * }
   *
   * var el = _.cloneDeepWith(document.body, customizer);
   *
   * console.log(el === document.body);
   * // => false
   * console.log(el.nodeName);
   * // => 'BODY'
   * console.log(el.childNodes.length);
   * // => 20
   */
  function cloneDeepWith(value, customizer) {
    customizer = typeof customizer == 'function' ? customizer : undefined
    return baseClone(
      value,
      CLONE_DEEP_FLAG$2 | CLONE_SYMBOLS_FLAG$3,
      customizer
    )
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_SYMBOLS_FLAG$4 = 4

  /**
   * This method is like `_.clone` except that it accepts `customizer` which
   * is invoked to produce the cloned value. If `customizer` returns `undefined`,
   * cloning is handled by the method instead. The `customizer` is invoked with
   * up to four arguments; (value [, index|key, object, stack]).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to clone.
   * @param {Function} [customizer] The function to customize cloning.
   * @returns {*} Returns the cloned value.
   * @see _.cloneDeepWith
   * @example
   *
   * function customizer(value) {
   *   if (_.isElement(value)) {
   *     return value.cloneNode(false);
   *   }
   * }
   *
   * var el = _.cloneWith(document.body, customizer);
   *
   * console.log(el === document.body);
   * // => false
   * console.log(el.nodeName);
   * // => 'BODY'
   * console.log(el.childNodes.length);
   * // => 0
   */
  function cloneWith(value, customizer) {
    customizer = typeof customizer == 'function' ? customizer : undefined
    return baseClone(value, CLONE_SYMBOLS_FLAG$4, customizer)
  }

  /**
   * Executes the chain sequence and returns the wrapped result.
   *
   * @name commit
   * @memberOf _
   * @since 3.2.0
   * @category Seq
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * var array = [1, 2];
   * var wrapped = _(array).push(3);
   *
   * console.log(array);
   * // => [1, 2]
   *
   * wrapped = wrapped.commit();
   * console.log(array);
   * // => [1, 2, 3]
   *
   * wrapped.last();
   * // => 3
   *
   * console.log(array);
   * // => [1, 2, 3]
   */
  function wrapperCommit() {
    return new LodashWrapper(this.value(), this.__chain__)
  }

  /**
   * Creates an array with all falsey values removed. The values `false`, `null`,
   * `0`, `""`, `undefined`, and `NaN` are falsey.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to compact.
   * @returns {Array} Returns the new array of filtered values.
   * @example
   *
   * _.compact([0, 1, false, 2, '', 3]);
   * // => [1, 2, 3]
   */
  function compact(array) {
    var index = -1,
      length = array == null ? 0 : array.length,
      resIndex = 0,
      result = []

    while (++index < length) {
      var value = array[index]
      if (value) {
        result[resIndex++] = value
      }
    }
    return result
  }

  /**
   * Creates a new array concatenating `array` with any additional arrays
   * and/or values.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to concatenate.
   * @param {...*} [values] The values to concatenate.
   * @returns {Array} Returns the new concatenated array.
   * @example
   *
   * var array = [1];
   * var other = _.concat(array, 2, [3], [[4]]);
   *
   * console.log(other);
   * // => [1, 2, 3, [4]]
   *
   * console.log(array);
   * // => [1]
   */
  function concat() {
    var length = arguments.length
    if (!length) {
      return []
    }
    var args = Array(length - 1),
      array = arguments[0],
      index = length

    while (index--) {
      args[index - 1] = arguments[index]
    }
    return arrayPush(
      isArray(array) ? copyArray(array) : [array],
      baseFlatten(args, 1)
    )
  }

  /** Used to stand-in for `undefined` hash values. */
  var HASH_UNDEFINED$2 = '__lodash_hash_undefined__'

  /**
   * Adds `value` to the array cache.
   *
   * @private
   * @name add
   * @memberOf SetCache
   * @alias push
   * @param {*} value The value to cache.
   * @returns {Object} Returns the cache instance.
   */
  function setCacheAdd(value) {
    this.__data__.set(value, HASH_UNDEFINED$2)
    return this
  }

  /**
   * Checks if `value` is in the array cache.
   *
   * @private
   * @name has
   * @memberOf SetCache
   * @param {*} value The value to search for.
   * @returns {number} Returns `true` if `value` is found, else `false`.
   */
  function setCacheHas(value) {
    return this.__data__.has(value)
  }

  /**
   *
   * Creates an array cache object to store unique values.
   *
   * @private
   * @constructor
   * @param {Array} [values] The values to cache.
   */
  function SetCache(values) {
    var index = -1,
      length = values == null ? 0 : values.length

    this.__data__ = new MapCache()
    while (++index < length) {
      this.add(values[index])
    }
  }

  // Add methods to `SetCache`.
  SetCache.prototype.add = SetCache.prototype.push = setCacheAdd
  SetCache.prototype.has = setCacheHas

  /**
   * A specialized version of `_.some` for arrays without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if any element passes the predicate check,
   *  else `false`.
   */
  function arraySome(array, predicate) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      if (predicate(array[index], index, array)) {
        return true
      }
    }
    return false
  }

  /**
   * Checks if a `cache` value for `key` exists.
   *
   * @private
   * @param {Object} cache The cache to query.
   * @param {string} key The key of the entry to check.
   * @returns {boolean} Returns `true` if an entry for `key` exists, else `false`.
   */
  function cacheHas(cache, key) {
    return cache.has(key)
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG = 1,
    COMPARE_UNORDERED_FLAG = 2

  /**
   * A specialized version of `baseIsEqualDeep` for arrays with support for
   * partial deep comparisons.
   *
   * @private
   * @param {Array} array The array to compare.
   * @param {Array} other The other array to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} stack Tracks traversed `array` and `other` objects.
   * @returns {boolean} Returns `true` if the arrays are equivalent, else `false`.
   */
  function equalArrays(array, other, bitmask, customizer, equalFunc, stack) {
    var isPartial = bitmask & COMPARE_PARTIAL_FLAG,
      arrLength = array.length,
      othLength = other.length

    if (arrLength != othLength && !(isPartial && othLength > arrLength)) {
      return false
    }
    // Assume cyclic values are equal.
    var stacked = stack.get(array)
    if (stacked && stack.get(other)) {
      return stacked == other
    }
    var index = -1,
      result = true,
      seen = bitmask & COMPARE_UNORDERED_FLAG ? new SetCache() : undefined

    stack.set(array, other)
    stack.set(other, array)

    // Ignore non-index properties.
    while (++index < arrLength) {
      var arrValue = array[index],
        othValue = other[index]

      if (customizer) {
        var compared = isPartial
          ? customizer(othValue, arrValue, index, other, array, stack)
          : customizer(arrValue, othValue, index, array, other, stack)
      }
      if (compared !== undefined) {
        if (compared) {
          continue
        }
        result = false
        break
      }
      // Recursively compare arrays (susceptible to call stack limits).
      if (seen) {
        if (
          !arraySome(other, function(othValue, othIndex) {
            if (
              !cacheHas(seen, othIndex) &&
              (arrValue === othValue ||
                equalFunc(arrValue, othValue, bitmask, customizer, stack))
            ) {
              return seen.push(othIndex)
            }
          })
        ) {
          result = false
          break
        }
      } else if (
        !(
          arrValue === othValue ||
          equalFunc(arrValue, othValue, bitmask, customizer, stack)
        )
      ) {
        result = false
        break
      }
    }
    stack['delete'](array)
    stack['delete'](other)
    return result
  }

  /**
   * Converts `map` to its key-value pairs.
   *
   * @private
   * @param {Object} map The map to convert.
   * @returns {Array} Returns the key-value pairs.
   */
  function mapToArray(map) {
    var index = -1,
      result = Array(map.size)

    map.forEach(function(value, key) {
      result[++index] = [key, value]
    })
    return result
  }

  /**
   * Converts `set` to an array of its values.
   *
   * @private
   * @param {Object} set The set to convert.
   * @returns {Array} Returns the values.
   */
  function setToArray(set) {
    var index = -1,
      result = Array(set.size)

    set.forEach(function(value) {
      result[++index] = value
    })
    return result
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$1 = 1,
    COMPARE_UNORDERED_FLAG$1 = 2

  /** `Object#toString` result references. */
  var boolTag$3 = '[object Boolean]',
    dateTag$3 = '[object Date]',
    errorTag$3 = '[object Error]',
    mapTag$5 = '[object Map]',
    numberTag$3 = '[object Number]',
    regexpTag$3 = '[object RegExp]',
    setTag$5 = '[object Set]',
    stringTag$3 = '[object String]',
    symbolTag$3 = '[object Symbol]'

  var arrayBufferTag$3 = '[object ArrayBuffer]',
    dataViewTag$4 = '[object DataView]'

  /** Used to convert symbols to primitives and strings. */
  var symbolProto$2 = Symbol$1 ? Symbol$1.prototype : undefined,
    symbolValueOf$1 = symbolProto$2 ? symbolProto$2.valueOf : undefined

  /**
   * A specialized version of `baseIsEqualDeep` for comparing objects of
   * the same `toStringTag`.
   *
   * **Note:** This function only supports comparing values with tags of
   * `Boolean`, `Date`, `Error`, `Number`, `RegExp`, or `String`.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {string} tag The `toStringTag` of the objects to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} stack Tracks traversed `object` and `other` objects.
   * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
   */
  function equalByTag(
    object,
    other,
    tag,
    bitmask,
    customizer,
    equalFunc,
    stack
  ) {
    switch (tag) {
      case dataViewTag$4:
        if (
          object.byteLength != other.byteLength ||
          object.byteOffset != other.byteOffset
        ) {
          return false
        }
        object = object.buffer
        other = other.buffer

      case arrayBufferTag$3:
        if (
          object.byteLength != other.byteLength ||
          !equalFunc(new Uint8Array(object), new Uint8Array(other))
        ) {
          return false
        }
        return true

      case boolTag$3:
      case dateTag$3:
      case numberTag$3:
        // Coerce booleans to `1` or `0` and dates to milliseconds.
        // Invalid dates are coerced to `NaN`.
        return eq$1(+object, +other)

      case errorTag$3:
        return object.name == other.name && object.message == other.message

      case regexpTag$3:
      case stringTag$3:
        // Coerce regexes to strings and treat strings, primitives and objects,
        // as equal. See http://www.ecma-international.org/ecma-262/7.0/#sec-regexp.prototype.tostring
        // for more details.
        return object == other + ''

      case mapTag$5:
        var convert = mapToArray

      case setTag$5:
        var isPartial = bitmask & COMPARE_PARTIAL_FLAG$1
        convert || (convert = setToArray)

        if (object.size != other.size && !isPartial) {
          return false
        }
        // Assume cyclic values are equal.
        var stacked = stack.get(object)
        if (stacked) {
          return stacked == other
        }
        bitmask |= COMPARE_UNORDERED_FLAG$1

        // Recursively compare objects (susceptible to call stack limits).
        stack.set(object, other)
        var result = equalArrays(
          convert(object),
          convert(other),
          bitmask,
          customizer,
          equalFunc,
          stack
        )
        stack['delete'](object)
        return result

      case symbolTag$3:
        if (symbolValueOf$1) {
          return symbolValueOf$1.call(object) == symbolValueOf$1.call(other)
        }
    }
    return false
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$2 = 1

  /** Used for built-in method references. */
  var objectProto$h = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$f = objectProto$h.hasOwnProperty

  /**
   * A specialized version of `baseIsEqualDeep` for objects with support for
   * partial deep comparisons.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} stack Tracks traversed `object` and `other` objects.
   * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
   */
  function equalObjects(object, other, bitmask, customizer, equalFunc, stack) {
    var isPartial = bitmask & COMPARE_PARTIAL_FLAG$2,
      objProps = getAllKeys(object),
      objLength = objProps.length,
      othProps = getAllKeys(other),
      othLength = othProps.length

    if (objLength != othLength && !isPartial) {
      return false
    }
    var index = objLength
    while (index--) {
      var key = objProps[index]
      if (!(isPartial ? key in other : hasOwnProperty$f.call(other, key))) {
        return false
      }
    }
    // Assume cyclic values are equal.
    var stacked = stack.get(object)
    if (stacked && stack.get(other)) {
      return stacked == other
    }
    var result = true
    stack.set(object, other)
    stack.set(other, object)

    var skipCtor = isPartial
    while (++index < objLength) {
      key = objProps[index]
      var objValue = object[key],
        othValue = other[key]

      if (customizer) {
        var compared = isPartial
          ? customizer(othValue, objValue, key, other, object, stack)
          : customizer(objValue, othValue, key, object, other, stack)
      }
      // Recursively compare objects (susceptible to call stack limits).
      if (
        !(compared === undefined
          ? objValue === othValue ||
            equalFunc(objValue, othValue, bitmask, customizer, stack)
          : compared)
      ) {
        result = false
        break
      }
      skipCtor || (skipCtor = key == 'constructor')
    }
    if (result && !skipCtor) {
      var objCtor = object.constructor,
        othCtor = other.constructor

      // Non `Object` object instances with different constructors are not equal.
      if (
        objCtor != othCtor &&
        ('constructor' in object && 'constructor' in other) &&
        !(
          typeof objCtor == 'function' &&
          objCtor instanceof objCtor &&
          typeof othCtor == 'function' &&
          othCtor instanceof othCtor
        )
      ) {
        result = false
      }
    }
    stack['delete'](object)
    stack['delete'](other)
    return result
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$3 = 1

  /** `Object#toString` result references. */
  var argsTag$3 = '[object Arguments]',
    arrayTag$2 = '[object Array]',
    objectTag$4 = '[object Object]'

  /** Used for built-in method references. */
  var objectProto$i = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$g = objectProto$i.hasOwnProperty

  /**
   * A specialized version of `baseIsEqual` for arrays and objects which performs
   * deep comparisons and tracks traversed objects enabling objects with circular
   * references to be compared.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {number} bitmask The bitmask flags. See `baseIsEqual` for more details.
   * @param {Function} customizer The function to customize comparisons.
   * @param {Function} equalFunc The function to determine equivalents of values.
   * @param {Object} [stack] Tracks traversed `object` and `other` objects.
   * @returns {boolean} Returns `true` if the objects are equivalent, else `false`.
   */
  function baseIsEqualDeep(
    object,
    other,
    bitmask,
    customizer,
    equalFunc,
    stack
  ) {
    var objIsArr = isArray(object),
      othIsArr = isArray(other),
      objTag = objIsArr ? arrayTag$2 : getTag$1(object),
      othTag = othIsArr ? arrayTag$2 : getTag$1(other)

    objTag = objTag == argsTag$3 ? objectTag$4 : objTag
    othTag = othTag == argsTag$3 ? objectTag$4 : othTag

    var objIsObj = objTag == objectTag$4,
      othIsObj = othTag == objectTag$4,
      isSameTag = objTag == othTag

    if (isSameTag && isBuffer(object)) {
      if (!isBuffer(other)) {
        return false
      }
      objIsArr = true
      objIsObj = false
    }
    if (isSameTag && !objIsObj) {
      stack || (stack = new Stack())
      return objIsArr || isTypedArray(object)
        ? equalArrays(object, other, bitmask, customizer, equalFunc, stack)
        : equalByTag(
            object,
            other,
            objTag,
            bitmask,
            customizer,
            equalFunc,
            stack
          )
    }
    if (!(bitmask & COMPARE_PARTIAL_FLAG$3)) {
      var objIsWrapped =
          objIsObj && hasOwnProperty$g.call(object, '__wrapped__'),
        othIsWrapped = othIsObj && hasOwnProperty$g.call(other, '__wrapped__')

      if (objIsWrapped || othIsWrapped) {
        var objUnwrapped = objIsWrapped ? object.value() : object,
          othUnwrapped = othIsWrapped ? other.value() : other

        stack || (stack = new Stack())
        return equalFunc(objUnwrapped, othUnwrapped, bitmask, customizer, stack)
      }
    }
    if (!isSameTag) {
      return false
    }
    stack || (stack = new Stack())
    return equalObjects(object, other, bitmask, customizer, equalFunc, stack)
  }

  /**
   * The base implementation of `_.isEqual` which supports partial comparisons
   * and tracks traversed objects.
   *
   * @private
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @param {boolean} bitmask The bitmask flags.
   *  1 - Unordered comparison
   *  2 - Partial comparison
   * @param {Function} [customizer] The function to customize comparisons.
   * @param {Object} [stack] Tracks traversed `value` and `other` objects.
   * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
   */
  function baseIsEqual(value, other, bitmask, customizer, stack) {
    if (value === other) {
      return true
    }
    if (
      value == null ||
      other == null ||
      (!isObjectLike(value) && !isObjectLike(other))
    ) {
      return value !== value && other !== other
    }
    return baseIsEqualDeep(
      value,
      other,
      bitmask,
      customizer,
      baseIsEqual,
      stack
    )
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$4 = 1,
    COMPARE_UNORDERED_FLAG$2 = 2

  /**
   * The base implementation of `_.isMatch` without support for iteratee shorthands.
   *
   * @private
   * @param {Object} object The object to inspect.
   * @param {Object} source The object of property values to match.
   * @param {Array} matchData The property names, values, and compare flags to match.
   * @param {Function} [customizer] The function to customize comparisons.
   * @returns {boolean} Returns `true` if `object` is a match, else `false`.
   */
  function baseIsMatch(object, source, matchData, customizer) {
    var index = matchData.length,
      length = index,
      noCustomizer = !customizer

    if (object == null) {
      return !length
    }
    object = Object(object)
    while (index--) {
      var data = matchData[index]
      if (
        noCustomizer && data[2]
          ? data[1] !== object[data[0]]
          : !(data[0] in object)
      ) {
        return false
      }
    }
    while (++index < length) {
      data = matchData[index]
      var key = data[0],
        objValue = object[key],
        srcValue = data[1]

      if (noCustomizer && data[2]) {
        if (objValue === undefined && !(key in object)) {
          return false
        }
      } else {
        var stack = new Stack()
        if (customizer) {
          var result = customizer(
            objValue,
            srcValue,
            key,
            object,
            source,
            stack
          )
        }
        if (
          !(result === undefined
            ? baseIsEqual(
                srcValue,
                objValue,
                COMPARE_PARTIAL_FLAG$4 | COMPARE_UNORDERED_FLAG$2,
                customizer,
                stack
              )
            : result)
        ) {
          return false
        }
      }
    }
    return true
  }

  /**
   * Checks if `value` is suitable for strict equality comparisons, i.e. `===`.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` if suitable for strict
   *  equality comparisons, else `false`.
   */
  function isStrictComparable(value) {
    return value === value && !isObject(value)
  }

  /**
   * Gets the property names, values, and compare flags of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @returns {Array} Returns the match data of `object`.
   */
  function getMatchData(object) {
    var result = keys(object),
      length = result.length

    while (length--) {
      var key = result[length],
        value = object[key]

      result[length] = [key, value, isStrictComparable(value)]
    }
    return result
  }

  /**
   * A specialized version of `matchesProperty` for source values suitable
   * for strict equality comparisons, i.e. `===`.
   *
   * @private
   * @param {string} key The key of the property to get.
   * @param {*} srcValue The value to match.
   * @returns {Function} Returns the new spec function.
   */
  function matchesStrictComparable(key, srcValue) {
    return function(object) {
      if (object == null) {
        return false
      }
      return (
        object[key] === srcValue &&
        (srcValue !== undefined || key in Object(object))
      )
    }
  }

  /**
   * The base implementation of `_.matches` which doesn't clone `source`.
   *
   * @private
   * @param {Object} source The object of property values to match.
   * @returns {Function} Returns the new spec function.
   */
  function baseMatches(source) {
    var matchData = getMatchData(source)
    if (matchData.length == 1 && matchData[0][2]) {
      return matchesStrictComparable(matchData[0][0], matchData[0][1])
    }
    return function(object) {
      return object === source || baseIsMatch(object, source, matchData)
    }
  }

  /**
   * The base implementation of `_.hasIn` without support for deep paths.
   *
   * @private
   * @param {Object} [object] The object to query.
   * @param {Array|string} key The key to check.
   * @returns {boolean} Returns `true` if `key` exists, else `false`.
   */
  function baseHasIn(object, key) {
    return object != null && key in Object(object)
  }

  /**
   * Checks if `path` exists on `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array|string} path The path to check.
   * @param {Function} hasFunc The function to check properties.
   * @returns {boolean} Returns `true` if `path` exists, else `false`.
   */
  function hasPath(object, path, hasFunc) {
    path = castPath(path, object)

    var index = -1,
      length = path.length,
      result = false

    while (++index < length) {
      var key = toKey(path[index])
      if (!(result = object != null && hasFunc(object, key))) {
        break
      }
      object = object[key]
    }
    if (result || ++index != length) {
      return result
    }
    length = object == null ? 0 : object.length
    return (
      !!length &&
      isLength(length) &&
      isIndex(key, length) &&
      (isArray(object) || isArguments(object))
    )
  }

  /**
   * Checks if `path` is a direct or inherited property of `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path to check.
   * @returns {boolean} Returns `true` if `path` exists, else `false`.
   * @example
   *
   * var object = _.create({ 'a': _.create({ 'b': 2 }) });
   *
   * _.hasIn(object, 'a');
   * // => true
   *
   * _.hasIn(object, 'a.b');
   * // => true
   *
   * _.hasIn(object, ['a', 'b']);
   * // => true
   *
   * _.hasIn(object, 'b');
   * // => false
   */
  function hasIn(object, path) {
    return object != null && hasPath(object, path, baseHasIn)
  }

  /** Used to compose bitmasks for value comparisons. */
  var COMPARE_PARTIAL_FLAG$5 = 1,
    COMPARE_UNORDERED_FLAG$3 = 2

  /**
   * The base implementation of `_.matchesProperty` which doesn't clone `srcValue`.
   *
   * @private
   * @param {string} path The path of the property to get.
   * @param {*} srcValue The value to match.
   * @returns {Function} Returns the new spec function.
   */
  function baseMatchesProperty(path, srcValue) {
    if (isKey(path) && isStrictComparable(srcValue)) {
      return matchesStrictComparable(toKey(path), srcValue)
    }
    return function(object) {
      var objValue = get(object, path)
      return objValue === undefined && objValue === srcValue
        ? hasIn(object, path)
        : baseIsEqual(
            srcValue,
            objValue,
            COMPARE_PARTIAL_FLAG$5 | COMPARE_UNORDERED_FLAG$3
          )
    }
  }

  /**
   * The base implementation of `_.property` without support for deep paths.
   *
   * @private
   * @param {string} key The key of the property to get.
   * @returns {Function} Returns the new accessor function.
   */
  function baseProperty(key) {
    return function(object) {
      return object == null ? undefined : object[key]
    }
  }

  /**
   * A specialized version of `baseProperty` which supports deep paths.
   *
   * @private
   * @param {Array|string} path The path of the property to get.
   * @returns {Function} Returns the new accessor function.
   */
  function basePropertyDeep(path) {
    return function(object) {
      return baseGet(object, path)
    }
  }

  /**
   * Creates a function that returns the value at `path` of a given object.
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Util
   * @param {Array|string} path The path of the property to get.
   * @returns {Function} Returns the new accessor function.
   * @example
   *
   * var objects = [
   *   { 'a': { 'b': 2 } },
   *   { 'a': { 'b': 1 } }
   * ];
   *
   * _.map(objects, _.property('a.b'));
   * // => [2, 1]
   *
   * _.map(_.sortBy(objects, _.property(['a', 'b'])), 'a.b');
   * // => [1, 2]
   */
  function property(path) {
    return isKey(path) ? baseProperty(toKey(path)) : basePropertyDeep(path)
  }

  /**
   * The base implementation of `_.iteratee`.
   *
   * @private
   * @param {*} [value=_.identity] The value to convert to an iteratee.
   * @returns {Function} Returns the iteratee.
   */
  function baseIteratee(value) {
    // Don't store the `typeof` result in a variable to avoid a JIT bug in Safari 9.
    // See https://bugs.webkit.org/show_bug.cgi?id=156034 for more details.
    if (typeof value == 'function') {
      return value
    }
    if (value == null) {
      return identity
    }
    if (typeof value == 'object') {
      return isArray(value)
        ? baseMatchesProperty(value[0], value[1])
        : baseMatches(value)
    }
    return property(value)
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$4 = 'Expected a function'

  /**
   * Creates a function that iterates over `pairs` and invokes the corresponding
   * function of the first predicate to return truthy. The predicate-function
   * pairs are invoked with the `this` binding and arguments of the created
   * function.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {Array} pairs The predicate-function pairs.
   * @returns {Function} Returns the new composite function.
   * @example
   *
   * var func = _.cond([
   *   [_.matches({ 'a': 1 }),           _.constant('matches A')],
   *   [_.conforms({ 'b': _.isNumber }), _.constant('matches B')],
   *   [_.stubTrue,                      _.constant('no match')]
   * ]);
   *
   * func({ 'a': 1, 'b': 2 });
   * // => 'matches A'
   *
   * func({ 'a': 0, 'b': 1 });
   * // => 'matches B'
   *
   * func({ 'a': '1', 'b': '2' });
   * // => 'no match'
   */
  function cond(pairs) {
    var length = pairs == null ? 0 : pairs.length,
      toIteratee = baseIteratee

    pairs = !length
      ? []
      : arrayMap(pairs, function(pair) {
          if (typeof pair[1] != 'function') {
            throw new TypeError(FUNC_ERROR_TEXT$4)
          }
          return [toIteratee(pair[0]), pair[1]]
        })

    return baseRest(function(args) {
      var index = -1
      while (++index < length) {
        var pair = pairs[index]
        if (apply(pair[0], this, args)) {
          return apply(pair[1], this, args)
        }
      }
    })
  }

  /**
   * The base implementation of `_.conformsTo` which accepts `props` to check.
   *
   * @private
   * @param {Object} object The object to inspect.
   * @param {Object} source The object of property predicates to conform to.
   * @returns {boolean} Returns `true` if `object` conforms, else `false`.
   */
  function baseConformsTo(object, source, props) {
    var length = props.length
    if (object == null) {
      return !length
    }
    object = Object(object)
    while (length--) {
      var key = props[length],
        predicate = source[key],
        value = object[key]

      if ((value === undefined && !(key in object)) || !predicate(value)) {
        return false
      }
    }
    return true
  }

  /**
   * The base implementation of `_.conforms` which doesn't clone `source`.
   *
   * @private
   * @param {Object} source The object of property predicates to conform to.
   * @returns {Function} Returns the new spec function.
   */
  function baseConforms(source) {
    var props = keys(source)
    return function(object) {
      return baseConformsTo(object, source, props)
    }
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$3 = 1

  /**
   * Creates a function that invokes the predicate properties of `source` with
   * the corresponding property values of a given object, returning `true` if
   * all predicates return truthy, else `false`.
   *
   * **Note:** The created function is equivalent to `_.conformsTo` with
   * `source` partially applied.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {Object} source The object of property predicates to conform to.
   * @returns {Function} Returns the new spec function.
   * @example
   *
   * var objects = [
   *   { 'a': 2, 'b': 1 },
   *   { 'a': 1, 'b': 2 }
   * ];
   *
   * _.filter(objects, _.conforms({ 'b': function(n) { return n > 1; } }));
   * // => [{ 'a': 1, 'b': 2 }]
   */
  function conforms(source) {
    return baseConforms(baseClone(source, CLONE_DEEP_FLAG$3))
  }

  /**
   * Checks if `object` conforms to `source` by invoking the predicate
   * properties of `source` with the corresponding property values of `object`.
   *
   * **Note:** This method is equivalent to `_.conforms` when `source` is
   * partially applied.
   *
   * @static
   * @memberOf _
   * @since 4.14.0
   * @category Lang
   * @param {Object} object The object to inspect.
   * @param {Object} source The object of property predicates to conform to.
   * @returns {boolean} Returns `true` if `object` conforms, else `false`.
   * @example
   *
   * var object = { 'a': 1, 'b': 2 };
   *
   * _.conformsTo(object, { 'b': function(n) { return n > 1; } });
   * // => true
   *
   * _.conformsTo(object, { 'b': function(n) { return n > 2; } });
   * // => false
   */
  function conformsTo(object, source) {
    return source == null || baseConformsTo(object, source, keys(source))
  }

  /**
   * A specialized version of `baseAggregator` for arrays.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} setter The function to set `accumulator` values.
   * @param {Function} iteratee The iteratee to transform keys.
   * @param {Object} accumulator The initial aggregated object.
   * @returns {Function} Returns `accumulator`.
   */
  function arrayAggregator(array, setter, iteratee, accumulator) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      var value = array[index]
      setter(accumulator, value, iteratee(value), array)
    }
    return accumulator
  }

  /**
   * Creates a base function for methods like `_.forIn` and `_.forOwn`.
   *
   * @private
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new base function.
   */
  function createBaseFor(fromRight) {
    return function(object, iteratee, keysFunc) {
      var index = -1,
        iterable = Object(object),
        props = keysFunc(object),
        length = props.length

      while (length--) {
        var key = props[fromRight ? length : ++index]
        if (iteratee(iterable[key], key, iterable) === false) {
          break
        }
      }
      return object
    }
  }

  /**
   * The base implementation of `baseForOwn` which iterates over `object`
   * properties returned by `keysFunc` and invokes `iteratee` for each property.
   * Iteratee functions may exit iteration early by explicitly returning `false`.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {Function} keysFunc The function to get the keys of `object`.
   * @returns {Object} Returns `object`.
   */
  var baseFor = createBaseFor()

  /**
   * The base implementation of `_.forOwn` without support for iteratee shorthands.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Object} Returns `object`.
   */
  function baseForOwn(object, iteratee) {
    return object && baseFor(object, iteratee, keys)
  }

  /**
   * Creates a `baseEach` or `baseEachRight` function.
   *
   * @private
   * @param {Function} eachFunc The function to iterate over a collection.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new base function.
   */
  function createBaseEach(eachFunc, fromRight) {
    return function(collection, iteratee) {
      if (collection == null) {
        return collection
      }
      if (!isArrayLike(collection)) {
        return eachFunc(collection, iteratee)
      }
      var length = collection.length,
        index = fromRight ? length : -1,
        iterable = Object(collection)

      while (fromRight ? index-- : ++index < length) {
        if (iteratee(iterable[index], index, iterable) === false) {
          break
        }
      }
      return collection
    }
  }

  /**
   * The base implementation of `_.forEach` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array|Object} Returns `collection`.
   */
  var baseEach = createBaseEach(baseForOwn)

  /**
   * Aggregates elements of `collection` on `accumulator` with keys transformed
   * by `iteratee` and values set by `setter`.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} setter The function to set `accumulator` values.
   * @param {Function} iteratee The iteratee to transform keys.
   * @param {Object} accumulator The initial aggregated object.
   * @returns {Function} Returns `accumulator`.
   */
  function baseAggregator(collection, setter, iteratee, accumulator) {
    baseEach(collection, function(value, key, collection) {
      setter(accumulator, value, iteratee(value), collection)
    })
    return accumulator
  }

  /**
   * Creates a function like `_.groupBy`.
   *
   * @private
   * @param {Function} setter The function to set accumulator values.
   * @param {Function} [initializer] The accumulator object initializer.
   * @returns {Function} Returns the new aggregator function.
   */
  function createAggregator(setter, initializer) {
    return function(collection, iteratee) {
      var func = isArray(collection) ? arrayAggregator : baseAggregator,
        accumulator = initializer ? initializer() : {}

      return func(collection, setter, baseIteratee(iteratee), accumulator)
    }
  }

  /** Used for built-in method references. */
  var objectProto$j = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$h = objectProto$j.hasOwnProperty

  /**
   * Creates an object composed of keys generated from the results of running
   * each element of `collection` thru `iteratee`. The corresponding value of
   * each key is the number of times the key was returned by `iteratee`. The
   * iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 0.5.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee to transform keys.
   * @returns {Object} Returns the composed aggregate object.
   * @example
   *
   * _.countBy([6.1, 4.2, 6.3], Math.floor);
   * // => { '4': 1, '6': 2 }
   *
   * // The `_.property` iteratee shorthand.
   * _.countBy(['one', 'two', 'three'], 'length');
   * // => { '3': 2, '5': 1 }
   */
  var countBy = createAggregator(function(result, value, key) {
    if (hasOwnProperty$h.call(result, key)) {
      ++result[key]
    } else {
      baseAssignValue(result, key, 1)
    }
  })

  /**
   * Creates an object that inherits from the `prototype` object. If a
   * `properties` object is given, its own enumerable string keyed properties
   * are assigned to the created object.
   *
   * @static
   * @memberOf _
   * @since 2.3.0
   * @category Object
   * @param {Object} prototype The object to inherit from.
   * @param {Object} [properties] The properties to assign to the object.
   * @returns {Object} Returns the new object.
   * @example
   *
   * function Shape() {
   *   this.x = 0;
   *   this.y = 0;
   * }
   *
   * function Circle() {
   *   Shape.call(this);
   * }
   *
   * Circle.prototype = _.create(Shape.prototype, {
   *   'constructor': Circle
   * });
   *
   * var circle = new Circle;
   * circle instanceof Circle;
   * // => true
   *
   * circle instanceof Shape;
   * // => true
   */
  function create(prototype, properties) {
    var result = baseCreate(prototype)
    return properties == null ? result : baseAssign(result, properties)
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_CURRY_FLAG$5 = 8

  /**
   * Creates a function that accepts arguments of `func` and either invokes
   * `func` returning its result, if at least `arity` number of arguments have
   * been provided, or returns a function that accepts the remaining `func`
   * arguments, and so on. The arity of `func` may be specified if `func.length`
   * is not sufficient.
   *
   * The `_.curry.placeholder` value, which defaults to `_` in monolithic builds,
   * may be used as a placeholder for provided arguments.
   *
   * **Note:** This method doesn't set the "length" property of curried functions.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Function
   * @param {Function} func The function to curry.
   * @param {number} [arity=func.length] The arity of `func`.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Function} Returns the new curried function.
   * @example
   *
   * var abc = function(a, b, c) {
   *   return [a, b, c];
   * };
   *
   * var curried = _.curry(abc);
   *
   * curried(1)(2)(3);
   * // => [1, 2, 3]
   *
   * curried(1, 2)(3);
   * // => [1, 2, 3]
   *
   * curried(1, 2, 3);
   * // => [1, 2, 3]
   *
   * // Curried with placeholders.
   * curried(1)(_, 3)(2);
   * // => [1, 2, 3]
   */
  function curry(func, arity, guard) {
    arity = guard ? undefined : arity
    var result = createWrap(
      func,
      WRAP_CURRY_FLAG$5,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      arity
    )
    result.placeholder = curry.placeholder
    return result
  }

  // Assign default placeholders.
  curry.placeholder = {}

  /** Used to compose bitmasks for function metadata. */
  var WRAP_CURRY_RIGHT_FLAG$3 = 16

  /**
   * This method is like `_.curry` except that arguments are applied to `func`
   * in the manner of `_.partialRight` instead of `_.partial`.
   *
   * The `_.curryRight.placeholder` value, which defaults to `_` in monolithic
   * builds, may be used as a placeholder for provided arguments.
   *
   * **Note:** This method doesn't set the "length" property of curried functions.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Function
   * @param {Function} func The function to curry.
   * @param {number} [arity=func.length] The arity of `func`.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Function} Returns the new curried function.
   * @example
   *
   * var abc = function(a, b, c) {
   *   return [a, b, c];
   * };
   *
   * var curried = _.curryRight(abc);
   *
   * curried(3)(2)(1);
   * // => [1, 2, 3]
   *
   * curried(2, 3)(1);
   * // => [1, 2, 3]
   *
   * curried(1, 2, 3);
   * // => [1, 2, 3]
   *
   * // Curried with placeholders.
   * curried(3)(1, _)(2);
   * // => [1, 2, 3]
   */
  function curryRight(func, arity, guard) {
    arity = guard ? undefined : arity
    var result = createWrap(
      func,
      WRAP_CURRY_RIGHT_FLAG$3,
      undefined,
      undefined,
      undefined,
      undefined,
      undefined,
      arity
    )
    result.placeholder = curryRight.placeholder
    return result
  }

  // Assign default placeholders.
  curryRight.placeholder = {}

  /**
   * Gets the timestamp of the number of milliseconds that have elapsed since
   * the Unix epoch (1 January 1970 00:00:00 UTC).
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Date
   * @returns {number} Returns the timestamp.
   * @example
   *
   * _.defer(function(stamp) {
   *   console.log(_.now() - stamp);
   * }, _.now());
   * // => Logs the number of milliseconds it took for the deferred invocation.
   */
  var now = function() {
    return root.Date.now()
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$5 = 'Expected a function'

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$5 = Math.max,
    nativeMin$3 = Math.min

  /**
   * Creates a debounced function that delays invoking `func` until after `wait`
   * milliseconds have elapsed since the last time the debounced function was
   * invoked. The debounced function comes with a `cancel` method to cancel
   * delayed `func` invocations and a `flush` method to immediately invoke them.
   * Provide `options` to indicate whether `func` should be invoked on the
   * leading and/or trailing edge of the `wait` timeout. The `func` is invoked
   * with the last arguments provided to the debounced function. Subsequent
   * calls to the debounced function return the result of the last `func`
   * invocation.
   *
   * **Note:** If `leading` and `trailing` options are `true`, `func` is
   * invoked on the trailing edge of the timeout only if the debounced function
   * is invoked more than once during the `wait` timeout.
   *
   * If `wait` is `0` and `leading` is `false`, `func` invocation is deferred
   * until to the next tick, similar to `setTimeout` with a timeout of `0`.
   *
   * See [David Corbacho's article](https://css-tricks.com/debouncing-throttling-explained-examples/)
   * for details over the differences between `_.debounce` and `_.throttle`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to debounce.
   * @param {number} [wait=0] The number of milliseconds to delay.
   * @param {Object} [options={}] The options object.
   * @param {boolean} [options.leading=false]
   *  Specify invoking on the leading edge of the timeout.
   * @param {number} [options.maxWait]
   *  The maximum time `func` is allowed to be delayed before it's invoked.
   * @param {boolean} [options.trailing=true]
   *  Specify invoking on the trailing edge of the timeout.
   * @returns {Function} Returns the new debounced function.
   * @example
   *
   * // Avoid costly calculations while the window size is in flux.
   * jQuery(window).on('resize', _.debounce(calculateLayout, 150));
   *
   * // Invoke `sendMail` when clicked, debouncing subsequent calls.
   * jQuery(element).on('click', _.debounce(sendMail, 300, {
   *   'leading': true,
   *   'trailing': false
   * }));
   *
   * // Ensure `batchLog` is invoked once after 1 second of debounced calls.
   * var debounced = _.debounce(batchLog, 250, { 'maxWait': 1000 });
   * var source = new EventSource('/stream');
   * jQuery(source).on('message', debounced);
   *
   * // Cancel the trailing debounced invocation.
   * jQuery(window).on('popstate', debounced.cancel);
   */
  function debounce(func, wait, options) {
    var lastArgs,
      lastThis,
      maxWait,
      result,
      timerId,
      lastCallTime,
      lastInvokeTime = 0,
      leading = false,
      maxing = false,
      trailing = true

    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$5)
    }
    wait = toNumber(wait) || 0
    if (isObject(options)) {
      leading = !!options.leading
      maxing = 'maxWait' in options
      maxWait = maxing
        ? nativeMax$5(toNumber(options.maxWait) || 0, wait)
        : maxWait
      trailing = 'trailing' in options ? !!options.trailing : trailing
    }

    function invokeFunc(time) {
      var args = lastArgs,
        thisArg = lastThis

      lastArgs = lastThis = undefined
      lastInvokeTime = time
      result = func.apply(thisArg, args)
      return result
    }

    function leadingEdge(time) {
      // Reset any `maxWait` timer.
      lastInvokeTime = time
      // Start the timer for the trailing edge.
      timerId = setTimeout(timerExpired, wait)
      // Invoke the leading edge.
      return leading ? invokeFunc(time) : result
    }

    function remainingWait(time) {
      var timeSinceLastCall = time - lastCallTime,
        timeSinceLastInvoke = time - lastInvokeTime,
        timeWaiting = wait - timeSinceLastCall

      return maxing
        ? nativeMin$3(timeWaiting, maxWait - timeSinceLastInvoke)
        : timeWaiting
    }

    function shouldInvoke(time) {
      var timeSinceLastCall = time - lastCallTime,
        timeSinceLastInvoke = time - lastInvokeTime

      // Either this is the first call, activity has stopped and we're at the
      // trailing edge, the system time has gone backwards and we're treating
      // it as the trailing edge, or we've hit the `maxWait` limit.
      return (
        lastCallTime === undefined ||
        timeSinceLastCall >= wait ||
        timeSinceLastCall < 0 ||
        (maxing && timeSinceLastInvoke >= maxWait)
      )
    }

    function timerExpired() {
      var time = now()
      if (shouldInvoke(time)) {
        return trailingEdge(time)
      }
      // Restart the timer.
      timerId = setTimeout(timerExpired, remainingWait(time))
    }

    function trailingEdge(time) {
      timerId = undefined

      // Only invoke if we have `lastArgs` which means `func` has been
      // debounced at least once.
      if (trailing && lastArgs) {
        return invokeFunc(time)
      }
      lastArgs = lastThis = undefined
      return result
    }

    function cancel() {
      if (timerId !== undefined) {
        clearTimeout(timerId)
      }
      lastInvokeTime = 0
      lastArgs = lastCallTime = lastThis = timerId = undefined
    }

    function flush() {
      return timerId === undefined ? result : trailingEdge(now())
    }

    function debounced() {
      var time = now(),
        isInvoking = shouldInvoke(time)

      lastArgs = arguments
      lastThis = this
      lastCallTime = time

      if (isInvoking) {
        if (timerId === undefined) {
          return leadingEdge(lastCallTime)
        }
        if (maxing) {
          // Handle invocations in a tight loop.
          clearTimeout(timerId)
          timerId = setTimeout(timerExpired, wait)
          return invokeFunc(lastCallTime)
        }
      }
      if (timerId === undefined) {
        timerId = setTimeout(timerExpired, wait)
      }
      return result
    }
    debounced.cancel = cancel
    debounced.flush = flush
    return debounced
  }

  /**
   * Checks `value` to determine whether a default value should be returned in
   * its place. The `defaultValue` is returned if `value` is `NaN`, `null`,
   * or `undefined`.
   *
   * @static
   * @memberOf _
   * @since 4.14.0
   * @category Util
   * @param {*} value The value to check.
   * @param {*} defaultValue The default value.
   * @returns {*} Returns the resolved value.
   * @example
   *
   * _.defaultTo(1, 10);
   * // => 1
   *
   * _.defaultTo(undefined, 10);
   * // => 10
   */
  function defaultTo(value, defaultValue) {
    return value == null || value !== value ? defaultValue : value
  }

  /** Used for built-in method references. */
  var objectProto$k = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$i = objectProto$k.hasOwnProperty

  /**
   * Assigns own and inherited enumerable string keyed properties of source
   * objects to the destination object for all destination properties that
   * resolve to `undefined`. Source objects are applied from left to right.
   * Once a property is set, additional values of the same property are ignored.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} [sources] The source objects.
   * @returns {Object} Returns `object`.
   * @see _.defaultsDeep
   * @example
   *
   * _.defaults({ 'a': 1 }, { 'b': 2 }, { 'a': 3 });
   * // => { 'a': 1, 'b': 2 }
   */
  var defaults = baseRest(function(object, sources) {
    object = Object(object)

    var index = -1
    var length = sources.length
    var guard = length > 2 ? sources[2] : undefined

    if (guard && isIterateeCall(sources[0], sources[1], guard)) {
      length = 1
    }

    while (++index < length) {
      var source = sources[index]
      var props = keysIn$1(source)
      var propsIndex = -1
      var propsLength = props.length

      while (++propsIndex < propsLength) {
        var key = props[propsIndex]
        var value = object[key]

        if (
          value === undefined ||
          (eq$1(value, objectProto$k[key]) &&
            !hasOwnProperty$i.call(object, key))
        ) {
          object[key] = source[key]
        }
      }
    }

    return object
  })

  /**
   * This function is like `assignValue` except that it doesn't assign
   * `undefined` values.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {string} key The key of the property to assign.
   * @param {*} value The value to assign.
   */
  function assignMergeValue(object, key, value) {
    if (
      (value !== undefined && !eq$1(object[key], value)) ||
      (value === undefined && !(key in object))
    ) {
      baseAssignValue(object, key, value)
    }
  }

  /**
   * This method is like `_.isArrayLike` except that it also checks if `value`
   * is an object.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an array-like object,
   *  else `false`.
   * @example
   *
   * _.isArrayLikeObject([1, 2, 3]);
   * // => true
   *
   * _.isArrayLikeObject(document.body.children);
   * // => true
   *
   * _.isArrayLikeObject('abc');
   * // => false
   *
   * _.isArrayLikeObject(_.noop);
   * // => false
   */
  function isArrayLikeObject(value) {
    return isObjectLike(value) && isArrayLike(value)
  }

  /**
   * Gets the value at `key`, unless `key` is "__proto__" or "constructor".
   *
   * @private
   * @param {Object} object The object to query.
   * @param {string} key The key of the property to get.
   * @returns {*} Returns the property value.
   */
  function safeGet(object, key) {
    if (key === 'constructor' && typeof object[key] === 'function') {
      return
    }

    if (key == '__proto__') {
      return
    }

    return object[key]
  }

  /**
   * Converts `value` to a plain object flattening inherited enumerable string
   * keyed properties of `value` to own properties of the plain object.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {Object} Returns the converted plain object.
   * @example
   *
   * function Foo() {
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.assign({ 'a': 1 }, new Foo);
   * // => { 'a': 1, 'b': 2 }
   *
   * _.assign({ 'a': 1 }, _.toPlainObject(new Foo));
   * // => { 'a': 1, 'b': 2, 'c': 3 }
   */
  function toPlainObject(value) {
    return copyObject(value, keysIn$1(value))
  }

  /**
   * A specialized version of `baseMerge` for arrays and objects which performs
   * deep merges and tracks traversed objects enabling objects with circular
   * references to be merged.
   *
   * @private
   * @param {Object} object The destination object.
   * @param {Object} source The source object.
   * @param {string} key The key of the value to merge.
   * @param {number} srcIndex The index of `source`.
   * @param {Function} mergeFunc The function to merge values.
   * @param {Function} [customizer] The function to customize assigned values.
   * @param {Object} [stack] Tracks traversed source values and their merged
   *  counterparts.
   */
  function baseMergeDeep(
    object,
    source,
    key,
    srcIndex,
    mergeFunc,
    customizer,
    stack
  ) {
    var objValue = safeGet(object, key),
      srcValue = safeGet(source, key),
      stacked = stack.get(srcValue)

    if (stacked) {
      assignMergeValue(object, key, stacked)
      return
    }
    var newValue = customizer
      ? customizer(objValue, srcValue, key + '', object, source, stack)
      : undefined

    var isCommon = newValue === undefined

    if (isCommon) {
      var isArr = isArray(srcValue),
        isBuff = !isArr && isBuffer(srcValue),
        isTyped = !isArr && !isBuff && isTypedArray(srcValue)

      newValue = srcValue
      if (isArr || isBuff || isTyped) {
        if (isArray(objValue)) {
          newValue = objValue
        } else if (isArrayLikeObject(objValue)) {
          newValue = copyArray(objValue)
        } else if (isBuff) {
          isCommon = false
          newValue = cloneBuffer(srcValue, true)
        } else if (isTyped) {
          isCommon = false
          newValue = cloneTypedArray(srcValue, true)
        } else {
          newValue = []
        }
      } else if (isPlainObject(srcValue) || isArguments(srcValue)) {
        newValue = objValue
        if (isArguments(objValue)) {
          newValue = toPlainObject(objValue)
        } else if (!isObject(objValue) || isFunction(objValue)) {
          newValue = initCloneObject(srcValue)
        }
      } else {
        isCommon = false
      }
    }
    if (isCommon) {
      // Recursively merge objects and arrays (susceptible to call stack limits).
      stack.set(srcValue, newValue)
      mergeFunc(newValue, srcValue, srcIndex, customizer, stack)
      stack['delete'](srcValue)
    }
    assignMergeValue(object, key, newValue)
  }

  /**
   * The base implementation of `_.merge` without support for multiple sources.
   *
   * @private
   * @param {Object} object The destination object.
   * @param {Object} source The source object.
   * @param {number} srcIndex The index of `source`.
   * @param {Function} [customizer] The function to customize merged values.
   * @param {Object} [stack] Tracks traversed source values and their merged
   *  counterparts.
   */
  function baseMerge(object, source, srcIndex, customizer, stack) {
    if (object === source) {
      return
    }
    baseFor(
      source,
      function(srcValue, key) {
        stack || (stack = new Stack())
        if (isObject(srcValue)) {
          baseMergeDeep(
            object,
            source,
            key,
            srcIndex,
            baseMerge,
            customizer,
            stack
          )
        } else {
          var newValue = customizer
            ? customizer(
                safeGet(object, key),
                srcValue,
                key + '',
                object,
                source,
                stack
              )
            : undefined

          if (newValue === undefined) {
            newValue = srcValue
          }
          assignMergeValue(object, key, newValue)
        }
      },
      keysIn$1
    )
  }

  /**
   * Used by `_.defaultsDeep` to customize its `_.merge` use to merge source
   * objects into destination objects that are passed thru.
   *
   * @private
   * @param {*} objValue The destination value.
   * @param {*} srcValue The source value.
   * @param {string} key The key of the property to merge.
   * @param {Object} object The parent object of `objValue`.
   * @param {Object} source The parent object of `srcValue`.
   * @param {Object} [stack] Tracks traversed source values and their merged
   *  counterparts.
   * @returns {*} Returns the value to assign.
   */
  function customDefaultsMerge(objValue, srcValue, key, object, source, stack) {
    if (isObject(objValue) && isObject(srcValue)) {
      // Recursively merge objects and arrays (susceptible to call stack limits).
      stack.set(srcValue, objValue)
      baseMerge(objValue, srcValue, undefined, customDefaultsMerge, stack)
      stack['delete'](srcValue)
    }
    return objValue
  }

  /**
   * This method is like `_.merge` except that it accepts `customizer` which
   * is invoked to produce the merged values of the destination and source
   * properties. If `customizer` returns `undefined`, merging is handled by the
   * method instead. The `customizer` is invoked with six arguments:
   * (objValue, srcValue, key, object, source, stack).
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} sources The source objects.
   * @param {Function} customizer The function to customize assigned values.
   * @returns {Object} Returns `object`.
   * @example
   *
   * function customizer(objValue, srcValue) {
   *   if (_.isArray(objValue)) {
   *     return objValue.concat(srcValue);
   *   }
   * }
   *
   * var object = { 'a': [1], 'b': [2] };
   * var other = { 'a': [3], 'b': [4] };
   *
   * _.mergeWith(object, other, customizer);
   * // => { 'a': [1, 3], 'b': [2, 4] }
   */
  var mergeWith = createAssigner(function(
    object,
    source,
    srcIndex,
    customizer
  ) {
    baseMerge(object, source, srcIndex, customizer)
  })

  /**
   * This method is like `_.defaults` except that it recursively assigns
   * default properties.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 3.10.0
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} [sources] The source objects.
   * @returns {Object} Returns `object`.
   * @see _.defaults
   * @example
   *
   * _.defaultsDeep({ 'a': { 'b': 2 } }, { 'a': { 'b': 1, 'c': 3 } });
   * // => { 'a': { 'b': 2, 'c': 3 } }
   */
  var defaultsDeep = baseRest(function(args) {
    args.push(undefined, customDefaultsMerge)
    return apply(mergeWith, undefined, args)
  })

  /** Error message constants. */
  var FUNC_ERROR_TEXT$6 = 'Expected a function'

  /**
   * The base implementation of `_.delay` and `_.defer` which accepts `args`
   * to provide to `func`.
   *
   * @private
   * @param {Function} func The function to delay.
   * @param {number} wait The number of milliseconds to delay invocation.
   * @param {Array} args The arguments to provide to `func`.
   * @returns {number|Object} Returns the timer id or timeout object.
   */
  function baseDelay(func, wait, args) {
    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$6)
    }
    return setTimeout(function() {
      func.apply(undefined, args)
    }, wait)
  }

  /**
   * Defers invoking the `func` until the current call stack has cleared. Any
   * additional arguments are provided to `func` when it's invoked.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to defer.
   * @param {...*} [args] The arguments to invoke `func` with.
   * @returns {number} Returns the timer id.
   * @example
   *
   * _.defer(function(text) {
   *   console.log(text);
   * }, 'deferred');
   * // => Logs 'deferred' after one millisecond.
   */
  var defer = baseRest(function(func, args) {
    return baseDelay(func, 1, args)
  })

  /**
   * Invokes `func` after `wait` milliseconds. Any additional arguments are
   * provided to `func` when it's invoked.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to delay.
   * @param {number} wait The number of milliseconds to delay invocation.
   * @param {...*} [args] The arguments to invoke `func` with.
   * @returns {number} Returns the timer id.
   * @example
   *
   * _.delay(function(text) {
   *   console.log(text);
   * }, 1000, 'later');
   * // => Logs 'later' after one second.
   */
  var delay = baseRest(function(func, wait, args) {
    return baseDelay(func, toNumber(wait) || 0, args)
  })

  /**
   * This function is like `arrayIncludes` except that it accepts a comparator.
   *
   * @private
   * @param {Array} [array] The array to inspect.
   * @param {*} target The value to search for.
   * @param {Function} comparator The comparator invoked per element.
   * @returns {boolean} Returns `true` if `target` is found, else `false`.
   */
  function arrayIncludesWith(array, value, comparator) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      if (comparator(value, array[index])) {
        return true
      }
    }
    return false
  }

  /** Used as the size to enable large array optimizations. */
  var LARGE_ARRAY_SIZE$1 = 200

  /**
   * The base implementation of methods like `_.difference` without support
   * for excluding multiple arrays or iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {Array} values The values to exclude.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of filtered values.
   */
  function baseDifference(array, values, iteratee, comparator) {
    var index = -1,
      includes = arrayIncludes,
      isCommon = true,
      length = array.length,
      result = [],
      valuesLength = values.length

    if (!length) {
      return result
    }
    if (iteratee) {
      values = arrayMap(values, baseUnary(iteratee))
    }
    if (comparator) {
      includes = arrayIncludesWith
      isCommon = false
    } else if (values.length >= LARGE_ARRAY_SIZE$1) {
      includes = cacheHas
      isCommon = false
      values = new SetCache(values)
    }
    outer: while (++index < length) {
      var value = array[index],
        computed = iteratee == null ? value : iteratee(value)

      value = comparator || value !== 0 ? value : 0
      if (isCommon && computed === computed) {
        var valuesIndex = valuesLength
        while (valuesIndex--) {
          if (values[valuesIndex] === computed) {
            continue outer
          }
        }
        result.push(value)
      } else if (!includes(values, computed, comparator)) {
        result.push(value)
      }
    }
    return result
  }

  /**
   * Creates an array of `array` values not included in the other given arrays
   * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons. The order and references of result values are
   * determined by the first array.
   *
   * **Note:** Unlike `_.pullAll`, this method returns a new array.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {...Array} [values] The values to exclude.
   * @returns {Array} Returns the new array of filtered values.
   * @see _.without, _.xor
   * @example
   *
   * _.difference([2, 1], [2, 3]);
   * // => [1]
   */
  var difference = baseRest(function(array, values) {
    return isArrayLikeObject(array)
      ? baseDifference(array, baseFlatten(values, 1, isArrayLikeObject, true))
      : []
  })

  /**
   * Gets the last element of `array`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to query.
   * @returns {*} Returns the last element of `array`.
   * @example
   *
   * _.last([1, 2, 3]);
   * // => 3
   */
  function last(array) {
    var length = array == null ? 0 : array.length
    return length ? array[length - 1] : undefined
  }

  /**
   * This method is like `_.difference` except that it accepts `iteratee` which
   * is invoked for each element of `array` and `values` to generate the criterion
   * by which they're compared. The order and references of result values are
   * determined by the first array. The iteratee is invoked with one argument:
   * (value).
   *
   * **Note:** Unlike `_.pullAllBy`, this method returns a new array.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {...Array} [values] The values to exclude.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Array} Returns the new array of filtered values.
   * @example
   *
   * _.differenceBy([2.1, 1.2], [2.3, 3.4], Math.floor);
   * // => [1.2]
   *
   * // The `_.property` iteratee shorthand.
   * _.differenceBy([{ 'x': 2 }, { 'x': 1 }], [{ 'x': 1 }], 'x');
   * // => [{ 'x': 2 }]
   */
  var differenceBy = baseRest(function(array, values) {
    var iteratee = last(values)
    if (isArrayLikeObject(iteratee)) {
      iteratee = undefined
    }
    return isArrayLikeObject(array)
      ? baseDifference(
          array,
          baseFlatten(values, 1, isArrayLikeObject, true),
          baseIteratee(iteratee)
        )
      : []
  })

  /**
   * This method is like `_.difference` except that it accepts `comparator`
   * which is invoked to compare elements of `array` to `values`. The order and
   * references of result values are determined by the first array. The comparator
   * is invoked with two arguments: (arrVal, othVal).
   *
   * **Note:** Unlike `_.pullAllWith`, this method returns a new array.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {...Array} [values] The values to exclude.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of filtered values.
   * @example
   *
   * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
   *
   * _.differenceWith(objects, [{ 'x': 1, 'y': 2 }], _.isEqual);
   * // => [{ 'x': 2, 'y': 1 }]
   */
  var differenceWith = baseRest(function(array, values) {
    var comparator = last(values)
    if (isArrayLikeObject(comparator)) {
      comparator = undefined
    }
    return isArrayLikeObject(array)
      ? baseDifference(
          array,
          baseFlatten(values, 1, isArrayLikeObject, true),
          undefined,
          comparator
        )
      : []
  })

  /**
   * Divide two numbers.
   *
   * @static
   * @memberOf _
   * @since 4.7.0
   * @category Math
   * @param {number} dividend The first number in a division.
   * @param {number} divisor The second number in a division.
   * @returns {number} Returns the quotient.
   * @example
   *
   * _.divide(6, 4);
   * // => 1.5
   */
  var divide = createMathOperation(function(dividend, divisor) {
    return dividend / divisor
  }, 1)

  /**
   * Creates a slice of `array` with `n` elements dropped from the beginning.
   *
   * @static
   * @memberOf _
   * @since 0.5.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {number} [n=1] The number of elements to drop.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * _.drop([1, 2, 3]);
   * // => [2, 3]
   *
   * _.drop([1, 2, 3], 2);
   * // => [3]
   *
   * _.drop([1, 2, 3], 5);
   * // => []
   *
   * _.drop([1, 2, 3], 0);
   * // => [1, 2, 3]
   */
  function drop(array, n, guard) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return []
    }
    n = guard || n === undefined ? 1 : toInteger(n)
    return baseSlice(array, n < 0 ? 0 : n, length)
  }

  /**
   * Creates a slice of `array` with `n` elements dropped from the end.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {number} [n=1] The number of elements to drop.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * _.dropRight([1, 2, 3]);
   * // => [1, 2]
   *
   * _.dropRight([1, 2, 3], 2);
   * // => [1]
   *
   * _.dropRight([1, 2, 3], 5);
   * // => []
   *
   * _.dropRight([1, 2, 3], 0);
   * // => [1, 2, 3]
   */
  function dropRight(array, n, guard) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return []
    }
    n = guard || n === undefined ? 1 : toInteger(n)
    n = length - n
    return baseSlice(array, 0, n < 0 ? 0 : n)
  }

  /**
   * The base implementation of methods like `_.dropWhile` and `_.takeWhile`
   * without support for iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to query.
   * @param {Function} predicate The function invoked per iteration.
   * @param {boolean} [isDrop] Specify dropping elements instead of taking them.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Array} Returns the slice of `array`.
   */
  function baseWhile(array, predicate, isDrop, fromRight) {
    var length = array.length,
      index = fromRight ? length : -1

    while (
      (fromRight ? index-- : ++index < length) &&
      predicate(array[index], index, array)
    ) {}

    return isDrop
      ? baseSlice(array, fromRight ? 0 : index, fromRight ? index + 1 : length)
      : baseSlice(array, fromRight ? index + 1 : 0, fromRight ? length : index)
  }

  /**
   * Creates a slice of `array` excluding elements dropped from the end.
   * Elements are dropped until `predicate` returns falsey. The predicate is
   * invoked with three arguments: (value, index, array).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': true },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': false }
   * ];
   *
   * _.dropRightWhile(users, function(o) { return !o.active; });
   * // => objects for ['barney']
   *
   * // The `_.matches` iteratee shorthand.
   * _.dropRightWhile(users, { 'user': 'pebbles', 'active': false });
   * // => objects for ['barney', 'fred']
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.dropRightWhile(users, ['active', false]);
   * // => objects for ['barney']
   *
   * // The `_.property` iteratee shorthand.
   * _.dropRightWhile(users, 'active');
   * // => objects for ['barney', 'fred', 'pebbles']
   */
  function dropRightWhile(array, predicate) {
    return array && array.length
      ? baseWhile(array, baseIteratee(predicate), true, true)
      : []
  }

  /**
   * Creates a slice of `array` excluding elements dropped from the beginning.
   * Elements are dropped until `predicate` returns falsey. The predicate is
   * invoked with three arguments: (value, index, array).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': false },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': true }
   * ];
   *
   * _.dropWhile(users, function(o) { return !o.active; });
   * // => objects for ['pebbles']
   *
   * // The `_.matches` iteratee shorthand.
   * _.dropWhile(users, { 'user': 'barney', 'active': false });
   * // => objects for ['fred', 'pebbles']
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.dropWhile(users, ['active', false]);
   * // => objects for ['pebbles']
   *
   * // The `_.property` iteratee shorthand.
   * _.dropWhile(users, 'active');
   * // => objects for ['barney', 'fred', 'pebbles']
   */
  function dropWhile(array, predicate) {
    return array && array.length
      ? baseWhile(array, baseIteratee(predicate), true)
      : []
  }

  /**
   * Casts `value` to `identity` if it's not a function.
   *
   * @private
   * @param {*} value The value to inspect.
   * @returns {Function} Returns cast function.
   */
  function castFunction(value) {
    return typeof value == 'function' ? value : identity
  }

  /**
   * Iterates over elements of `collection` and invokes `iteratee` for each element.
   * The iteratee is invoked with three arguments: (value, index|key, collection).
   * Iteratee functions may exit iteration early by explicitly returning `false`.
   *
   * **Note:** As with other "Collections" methods, objects with a "length"
   * property are iterated like arrays. To avoid this behavior use `_.forIn`
   * or `_.forOwn` for object iteration.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @alias each
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Array|Object} Returns `collection`.
   * @see _.forEachRight
   * @example
   *
   * _.forEach([1, 2], function(value) {
   *   console.log(value);
   * });
   * // => Logs `1` then `2`.
   *
   * _.forEach({ 'a': 1, 'b': 2 }, function(value, key) {
   *   console.log(key);
   * });
   * // => Logs 'a' then 'b' (iteration order is not guaranteed).
   */
  function forEach(collection, iteratee) {
    var func = isArray(collection) ? arrayEach : baseEach
    return func(collection, castFunction(iteratee))
  }

  /**
   * A specialized version of `_.forEachRight` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns `array`.
   */
  function arrayEachRight(array, iteratee) {
    var length = array == null ? 0 : array.length

    while (length--) {
      if (iteratee(array[length], length, array) === false) {
        break
      }
    }
    return array
  }

  /**
   * This function is like `baseFor` except that it iterates over properties
   * in the opposite order.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {Function} keysFunc The function to get the keys of `object`.
   * @returns {Object} Returns `object`.
   */
  var baseForRight = createBaseFor(true)

  /**
   * The base implementation of `_.forOwnRight` without support for iteratee shorthands.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Object} Returns `object`.
   */
  function baseForOwnRight(object, iteratee) {
    return object && baseForRight(object, iteratee, keys)
  }

  /**
   * The base implementation of `_.forEachRight` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array|Object} Returns `collection`.
   */
  var baseEachRight = createBaseEach(baseForOwnRight, true)

  /**
   * This method is like `_.forEach` except that it iterates over elements of
   * `collection` from right to left.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @alias eachRight
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Array|Object} Returns `collection`.
   * @see _.forEach
   * @example
   *
   * _.forEachRight([1, 2], function(value) {
   *   console.log(value);
   * });
   * // => Logs `2` then `1`.
   */
  function forEachRight(collection, iteratee) {
    var func = isArray(collection) ? arrayEachRight : baseEachRight
    return func(collection, castFunction(iteratee))
  }

  /**
   * Checks if `string` ends with the given target string.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to inspect.
   * @param {string} [target] The string to search for.
   * @param {number} [position=string.length] The position to search up to.
   * @returns {boolean} Returns `true` if `string` ends with `target`,
   *  else `false`.
   * @example
   *
   * _.endsWith('abc', 'c');
   * // => true
   *
   * _.endsWith('abc', 'b');
   * // => false
   *
   * _.endsWith('abc', 'b', 2);
   * // => true
   */
  function endsWith(string, target, position) {
    string = toString(string)
    target = baseToString(target)

    var length = string.length
    position =
      position === undefined
        ? length
        : baseClamp(toInteger(position), 0, length)

    var end = position
    position -= target.length
    return position >= 0 && string.slice(position, end) == target
  }

  /**
   * The base implementation of `_.toPairs` and `_.toPairsIn` which creates an array
   * of key-value pairs for `object` corresponding to the property names of `props`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array} props The property names to get values for.
   * @returns {Object} Returns the key-value pairs.
   */
  function baseToPairs(object, props) {
    return arrayMap(props, function(key) {
      return [key, object[key]]
    })
  }

  /**
   * Converts `set` to its value-value pairs.
   *
   * @private
   * @param {Object} set The set to convert.
   * @returns {Array} Returns the value-value pairs.
   */
  function setToPairs(set) {
    var index = -1,
      result = Array(set.size)

    set.forEach(function(value) {
      result[++index] = [value, value]
    })
    return result
  }

  /** `Object#toString` result references. */
  var mapTag$6 = '[object Map]',
    setTag$6 = '[object Set]'

  /**
   * Creates a `_.toPairs` or `_.toPairsIn` function.
   *
   * @private
   * @param {Function} keysFunc The function to get the keys of a given object.
   * @returns {Function} Returns the new pairs function.
   */
  function createToPairs(keysFunc) {
    return function(object) {
      var tag = getTag$1(object)
      if (tag == mapTag$6) {
        return mapToArray(object)
      }
      if (tag == setTag$6) {
        return setToPairs(object)
      }
      return baseToPairs(object, keysFunc(object))
    }
  }

  /**
   * Creates an array of own enumerable string keyed-value pairs for `object`
   * which can be consumed by `_.fromPairs`. If `object` is a map or set, its
   * entries are returned.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @alias entries
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the key-value pairs.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.toPairs(new Foo);
   * // => [['a', 1], ['b', 2]] (iteration order is not guaranteed)
   */
  var toPairs = createToPairs(keys)

  /**
   * Creates an array of own and inherited enumerable string keyed-value pairs
   * for `object` which can be consumed by `_.fromPairs`. If `object` is a map
   * or set, its entries are returned.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @alias entriesIn
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the key-value pairs.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.toPairsIn(new Foo);
   * // => [['a', 1], ['b', 2], ['c', 3]] (iteration order is not guaranteed)
   */
  var toPairsIn = createToPairs(keysIn$1)

  /** Used to map characters to HTML entities. */
  var htmlEscapes = {
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;',
    "'": '&#39;',
  }

  /**
   * Used by `_.escape` to convert characters to HTML entities.
   *
   * @private
   * @param {string} chr The matched character to escape.
   * @returns {string} Returns the escaped character.
   */
  var escapeHtmlChar = basePropertyOf(htmlEscapes)

  /** Used to match HTML entities and HTML characters. */
  var reUnescapedHtml = /[&<>"']/g,
    reHasUnescapedHtml = RegExp(reUnescapedHtml.source)

  /**
   * Converts the characters "&", "<", ">", '"', and "'" in `string` to their
   * corresponding HTML entities.
   *
   * **Note:** No other characters are escaped. To escape additional
   * characters use a third-party library like [_he_](https://mths.be/he).
   *
   * Though the ">" character is escaped for symmetry, characters like
   * ">" and "/" don't need escaping in HTML and have no special meaning
   * unless they're part of a tag or unquoted attribute value. See
   * [Mathias Bynens's article](https://mathiasbynens.be/notes/ambiguous-ampersands)
   * (under "semi-related fun fact") for more details.
   *
   * When working with HTML you should always
   * [quote attribute values](http://wonko.com/post/html-escaping) to reduce
   * XSS vectors.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category String
   * @param {string} [string=''] The string to escape.
   * @returns {string} Returns the escaped string.
   * @example
   *
   * _.escape('fred, barney, & pebbles');
   * // => 'fred, barney, &amp; pebbles'
   */
  function escape(string) {
    string = toString(string)
    return string && reHasUnescapedHtml.test(string)
      ? string.replace(reUnescapedHtml, escapeHtmlChar)
      : string
  }

  /**
   * Used to match `RegExp`
   * [syntax characters](http://ecma-international.org/ecma-262/7.0/#sec-patterns).
   */
  var reRegExpChar$1 = /[\\^$.*+?()[\]{}|]/g,
    reHasRegExpChar = RegExp(reRegExpChar$1.source)

  /**
   * Escapes the `RegExp` special characters "^", "$", "\", ".", "*", "+",
   * "?", "(", ")", "[", "]", "{", "}", and "|" in `string`.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to escape.
   * @returns {string} Returns the escaped string.
   * @example
   *
   * _.escapeRegExp('[lodash](https://lodash.com/)');
   * // => '\[lodash\]\(https://lodash\.com/\)'
   */
  function escapeRegExp(string) {
    string = toString(string)
    return string && reHasRegExpChar.test(string)
      ? string.replace(reRegExpChar$1, '\\$&')
      : string
  }

  /**
   * A specialized version of `_.every` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if all elements pass the predicate check,
   *  else `false`.
   */
  function arrayEvery(array, predicate) {
    var index = -1,
      length = array == null ? 0 : array.length

    while (++index < length) {
      if (!predicate(array[index], index, array)) {
        return false
      }
    }
    return true
  }

  /**
   * The base implementation of `_.every` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if all elements pass the predicate check,
   *  else `false`
   */
  function baseEvery(collection, predicate) {
    var result = true
    baseEach(collection, function(value, index, collection) {
      result = !!predicate(value, index, collection)
      return result
    })
    return result
  }

  /**
   * Checks if `predicate` returns truthy for **all** elements of `collection`.
   * Iteration is stopped once `predicate` returns falsey. The predicate is
   * invoked with three arguments: (value, index|key, collection).
   *
   * **Note:** This method returns `true` for
   * [empty collections](https://en.wikipedia.org/wiki/Empty_set) because
   * [everything is true](https://en.wikipedia.org/wiki/Vacuous_truth) of
   * elements of empty collections.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {boolean} Returns `true` if all elements pass the predicate check,
   *  else `false`.
   * @example
   *
   * _.every([true, 1, null, 'yes'], Boolean);
   * // => false
   *
   * var users = [
   *   { 'user': 'barney', 'age': 36, 'active': false },
   *   { 'user': 'fred',   'age': 40, 'active': false }
   * ];
   *
   * // The `_.matches` iteratee shorthand.
   * _.every(users, { 'user': 'barney', 'active': false });
   * // => false
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.every(users, ['active', false]);
   * // => true
   *
   * // The `_.property` iteratee shorthand.
   * _.every(users, 'active');
   * // => false
   */
  function every(collection, predicate, guard) {
    var func = isArray(collection) ? arrayEvery : baseEvery
    if (guard && isIterateeCall(collection, predicate, guard)) {
      predicate = undefined
    }
    return func(collection, baseIteratee(predicate))
  }

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH$1 = 4294967295

  /**
   * Converts `value` to an integer suitable for use as the length of an
   * array-like object.
   *
   * **Note:** This method is based on
   * [`ToLength`](http://ecma-international.org/ecma-262/7.0/#sec-tolength).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {number} Returns the converted integer.
   * @example
   *
   * _.toLength(3.2);
   * // => 3
   *
   * _.toLength(Number.MIN_VALUE);
   * // => 0
   *
   * _.toLength(Infinity);
   * // => 4294967295
   *
   * _.toLength('3.2');
   * // => 3
   */
  function toLength(value) {
    return value ? baseClamp(toInteger(value), 0, MAX_ARRAY_LENGTH$1) : 0
  }

  /**
   * The base implementation of `_.fill` without an iteratee call guard.
   *
   * @private
   * @param {Array} array The array to fill.
   * @param {*} value The value to fill `array` with.
   * @param {number} [start=0] The start position.
   * @param {number} [end=array.length] The end position.
   * @returns {Array} Returns `array`.
   */
  function baseFill(array, value, start, end) {
    var length = array.length

    start = toInteger(start)
    if (start < 0) {
      start = -start > length ? 0 : length + start
    }
    end = end === undefined || end > length ? length : toInteger(end)
    if (end < 0) {
      end += length
    }
    end = start > end ? 0 : toLength(end)
    while (start < end) {
      array[start++] = value
    }
    return array
  }

  /**
   * Fills elements of `array` with `value` from `start` up to, but not
   * including, `end`.
   *
   * **Note:** This method mutates `array`.
   *
   * @static
   * @memberOf _
   * @since 3.2.0
   * @category Array
   * @param {Array} array The array to fill.
   * @param {*} value The value to fill `array` with.
   * @param {number} [start=0] The start position.
   * @param {number} [end=array.length] The end position.
   * @returns {Array} Returns `array`.
   * @example
   *
   * var array = [1, 2, 3];
   *
   * _.fill(array, 'a');
   * console.log(array);
   * // => ['a', 'a', 'a']
   *
   * _.fill(Array(3), 2);
   * // => [2, 2, 2]
   *
   * _.fill([4, 6, 8, 10], '*', 1, 3);
   * // => [4, '*', '*', 10]
   */
  function fill(array, value, start, end) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return []
    }
    if (
      start &&
      typeof start != 'number' &&
      isIterateeCall(array, value, start)
    ) {
      start = 0
      end = length
    }
    return baseFill(array, value, start, end)
  }

  /**
   * The base implementation of `_.filter` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {Array} Returns the new filtered array.
   */
  function baseFilter(collection, predicate) {
    var result = []
    baseEach(collection, function(value, index, collection) {
      if (predicate(value, index, collection)) {
        result.push(value)
      }
    })
    return result
  }

  /**
   * Iterates over elements of `collection`, returning an array of all elements
   * `predicate` returns truthy for. The predicate is invoked with three
   * arguments: (value, index|key, collection).
   *
   * **Note:** Unlike `_.remove`, this method returns a new array.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the new filtered array.
   * @see _.reject
   * @example
   *
   * var users = [
   *   { 'user': 'barney', 'age': 36, 'active': true },
   *   { 'user': 'fred',   'age': 40, 'active': false }
   * ];
   *
   * _.filter(users, function(o) { return !o.active; });
   * // => objects for ['fred']
   *
   * // The `_.matches` iteratee shorthand.
   * _.filter(users, { 'age': 36, 'active': true });
   * // => objects for ['barney']
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.filter(users, ['active', false]);
   * // => objects for ['fred']
   *
   * // The `_.property` iteratee shorthand.
   * _.filter(users, 'active');
   * // => objects for ['barney']
   */
  function filter(collection, predicate) {
    var func = isArray(collection) ? arrayFilter : baseFilter
    return func(collection, baseIteratee(predicate))
  }

  /**
   * Creates a `_.find` or `_.findLast` function.
   *
   * @private
   * @param {Function} findIndexFunc The function to find the collection index.
   * @returns {Function} Returns the new find function.
   */
  function createFind(findIndexFunc) {
    return function(collection, predicate, fromIndex) {
      var iterable = Object(collection)
      if (!isArrayLike(collection)) {
        var iteratee = baseIteratee(predicate)
        collection = keys(collection)
        predicate = function(key) {
          return iteratee(iterable[key], key, iterable)
        }
      }
      var index = findIndexFunc(collection, predicate, fromIndex)
      return index > -1
        ? iterable[iteratee ? collection[index] : index]
        : undefined
    }
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$6 = Math.max

  /**
   * This method is like `_.find` except that it returns the index of the first
   * element `predicate` returns truthy for instead of the element itself.
   *
   * @static
   * @memberOf _
   * @since 1.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param {number} [fromIndex=0] The index to search from.
   * @returns {number} Returns the index of the found element, else `-1`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': false },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': true }
   * ];
   *
   * _.findIndex(users, function(o) { return o.user == 'barney'; });
   * // => 0
   *
   * // The `_.matches` iteratee shorthand.
   * _.findIndex(users, { 'user': 'fred', 'active': false });
   * // => 1
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.findIndex(users, ['active', false]);
   * // => 0
   *
   * // The `_.property` iteratee shorthand.
   * _.findIndex(users, 'active');
   * // => 2
   */
  function findIndex(array, predicate, fromIndex) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return -1
    }
    var index = fromIndex == null ? 0 : toInteger(fromIndex)
    if (index < 0) {
      index = nativeMax$6(length + index, 0)
    }
    return baseFindIndex(array, baseIteratee(predicate), index)
  }

  /**
   * Iterates over elements of `collection`, returning the first element
   * `predicate` returns truthy for. The predicate is invoked with three
   * arguments: (value, index|key, collection).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param {number} [fromIndex=0] The index to search from.
   * @returns {*} Returns the matched element, else `undefined`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'age': 36, 'active': true },
   *   { 'user': 'fred',    'age': 40, 'active': false },
   *   { 'user': 'pebbles', 'age': 1,  'active': true }
   * ];
   *
   * _.find(users, function(o) { return o.age < 40; });
   * // => object for 'barney'
   *
   * // The `_.matches` iteratee shorthand.
   * _.find(users, { 'age': 1, 'active': true });
   * // => object for 'pebbles'
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.find(users, ['active', false]);
   * // => object for 'fred'
   *
   * // The `_.property` iteratee shorthand.
   * _.find(users, 'active');
   * // => object for 'barney'
   */
  var find = createFind(findIndex)

  /**
   * The base implementation of methods like `_.findKey` and `_.findLastKey`,
   * without support for iteratee shorthands, which iterates over `collection`
   * using `eachFunc`.
   *
   * @private
   * @param {Array|Object} collection The collection to inspect.
   * @param {Function} predicate The function invoked per iteration.
   * @param {Function} eachFunc The function to iterate over `collection`.
   * @returns {*} Returns the found element or its key, else `undefined`.
   */
  function baseFindKey(collection, predicate, eachFunc) {
    var result
    eachFunc(collection, function(value, key, collection) {
      if (predicate(value, key, collection)) {
        result = key
        return false
      }
    })
    return result
  }

  /**
   * This method is like `_.find` except that it returns the key of the first
   * element `predicate` returns truthy for instead of the element itself.
   *
   * @static
   * @memberOf _
   * @since 1.1.0
   * @category Object
   * @param {Object} object The object to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {string|undefined} Returns the key of the matched element,
   *  else `undefined`.
   * @example
   *
   * var users = {
   *   'barney':  { 'age': 36, 'active': true },
   *   'fred':    { 'age': 40, 'active': false },
   *   'pebbles': { 'age': 1,  'active': true }
   * };
   *
   * _.findKey(users, function(o) { return o.age < 40; });
   * // => 'barney' (iteration order is not guaranteed)
   *
   * // The `_.matches` iteratee shorthand.
   * _.findKey(users, { 'age': 1, 'active': true });
   * // => 'pebbles'
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.findKey(users, ['active', false]);
   * // => 'fred'
   *
   * // The `_.property` iteratee shorthand.
   * _.findKey(users, 'active');
   * // => 'barney'
   */
  function findKey(object, predicate) {
    return baseFindKey(object, baseIteratee(predicate), baseForOwn)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$7 = Math.max,
    nativeMin$4 = Math.min

  /**
   * This method is like `_.findIndex` except that it iterates over elements
   * of `collection` from right to left.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param {number} [fromIndex=array.length-1] The index to search from.
   * @returns {number} Returns the index of the found element, else `-1`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': true },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': false }
   * ];
   *
   * _.findLastIndex(users, function(o) { return o.user == 'pebbles'; });
   * // => 2
   *
   * // The `_.matches` iteratee shorthand.
   * _.findLastIndex(users, { 'user': 'barney', 'active': true });
   * // => 0
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.findLastIndex(users, ['active', false]);
   * // => 2
   *
   * // The `_.property` iteratee shorthand.
   * _.findLastIndex(users, 'active');
   * // => 0
   */
  function findLastIndex(array, predicate, fromIndex) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return -1
    }
    var index = length - 1
    if (fromIndex !== undefined) {
      index = toInteger(fromIndex)
      index =
        fromIndex < 0
          ? nativeMax$7(length + index, 0)
          : nativeMin$4(index, length - 1)
    }
    return baseFindIndex(array, baseIteratee(predicate), index, true)
  }

  /**
   * This method is like `_.find` except that it iterates over elements of
   * `collection` from right to left.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param {number} [fromIndex=collection.length-1] The index to search from.
   * @returns {*} Returns the matched element, else `undefined`.
   * @example
   *
   * _.findLast([1, 2, 3, 4], function(n) {
   *   return n % 2 == 1;
   * });
   * // => 3
   */
  var findLast = createFind(findLastIndex)

  /**
   * This method is like `_.findKey` except that it iterates over elements of
   * a collection in the opposite order.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Object
   * @param {Object} object The object to inspect.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {string|undefined} Returns the key of the matched element,
   *  else `undefined`.
   * @example
   *
   * var users = {
   *   'barney':  { 'age': 36, 'active': true },
   *   'fred':    { 'age': 40, 'active': false },
   *   'pebbles': { 'age': 1,  'active': true }
   * };
   *
   * _.findLastKey(users, function(o) { return o.age < 40; });
   * // => returns 'pebbles' assuming `_.findKey` returns 'barney'
   *
   * // The `_.matches` iteratee shorthand.
   * _.findLastKey(users, { 'age': 36, 'active': true });
   * // => 'barney'
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.findLastKey(users, ['active', false]);
   * // => 'fred'
   *
   * // The `_.property` iteratee shorthand.
   * _.findLastKey(users, 'active');
   * // => 'pebbles'
   */
  function findLastKey(object, predicate) {
    return baseFindKey(object, baseIteratee(predicate), baseForOwnRight)
  }

  /**
   * Gets the first element of `array`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @alias first
   * @category Array
   * @param {Array} array The array to query.
   * @returns {*} Returns the first element of `array`.
   * @example
   *
   * _.head([1, 2, 3]);
   * // => 1
   *
   * _.head([]);
   * // => undefined
   */
  function head(array) {
    return array && array.length ? array[0] : undefined
  }

  /**
   * The base implementation of `_.map` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {Array} Returns the new mapped array.
   */
  function baseMap(collection, iteratee) {
    var index = -1,
      result = isArrayLike(collection) ? Array(collection.length) : []

    baseEach(collection, function(value, key, collection) {
      result[++index] = iteratee(value, key, collection)
    })
    return result
  }

  /**
   * Creates an array of values by running each element in `collection` thru
   * `iteratee`. The iteratee is invoked with three arguments:
   * (value, index|key, collection).
   *
   * Many lodash methods are guarded to work as iteratees for methods like
   * `_.every`, `_.filter`, `_.map`, `_.mapValues`, `_.reject`, and `_.some`.
   *
   * The guarded methods are:
   * `ary`, `chunk`, `curry`, `curryRight`, `drop`, `dropRight`, `every`,
   * `fill`, `invert`, `parseInt`, `random`, `range`, `rangeRight`, `repeat`,
   * `sampleSize`, `slice`, `some`, `sortBy`, `split`, `take`, `takeRight`,
   * `template`, `trim`, `trimEnd`, `trimStart`, and `words`
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the new mapped array.
   * @example
   *
   * function square(n) {
   *   return n * n;
   * }
   *
   * _.map([4, 8], square);
   * // => [16, 64]
   *
   * _.map({ 'a': 4, 'b': 8 }, square);
   * // => [16, 64] (iteration order is not guaranteed)
   *
   * var users = [
   *   { 'user': 'barney' },
   *   { 'user': 'fred' }
   * ];
   *
   * // The `_.property` iteratee shorthand.
   * _.map(users, 'user');
   * // => ['barney', 'fred']
   */
  function map(collection, iteratee) {
    var func = isArray(collection) ? arrayMap : baseMap
    return func(collection, baseIteratee(iteratee))
  }

  /**
   * Creates a flattened array of values by running each element in `collection`
   * thru `iteratee` and flattening the mapped results. The iteratee is invoked
   * with three arguments: (value, index|key, collection).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * function duplicate(n) {
   *   return [n, n];
   * }
   *
   * _.flatMap([1, 2], duplicate);
   * // => [1, 1, 2, 2]
   */
  function flatMap(collection, iteratee) {
    return baseFlatten(map(collection, iteratee), 1)
  }

  /** Used as references for various `Number` constants. */
  var INFINITY$3 = 1 / 0

  /**
   * This method is like `_.flatMap` except that it recursively flattens the
   * mapped results.
   *
   * @static
   * @memberOf _
   * @since 4.7.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * function duplicate(n) {
   *   return [[[n, n]]];
   * }
   *
   * _.flatMapDeep([1, 2], duplicate);
   * // => [1, 1, 2, 2]
   */
  function flatMapDeep(collection, iteratee) {
    return baseFlatten(map(collection, iteratee), INFINITY$3)
  }

  /**
   * This method is like `_.flatMap` except that it recursively flattens the
   * mapped results up to `depth` times.
   *
   * @static
   * @memberOf _
   * @since 4.7.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @param {number} [depth=1] The maximum recursion depth.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * function duplicate(n) {
   *   return [[[n, n]]];
   * }
   *
   * _.flatMapDepth([1, 2], duplicate, 2);
   * // => [[1, 1], [2, 2]]
   */
  function flatMapDepth(collection, iteratee, depth) {
    depth = depth === undefined ? 1 : toInteger(depth)
    return baseFlatten(map(collection, iteratee), depth)
  }

  /** Used as references for various `Number` constants. */
  var INFINITY$4 = 1 / 0

  /**
   * Recursively flattens `array`.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to flatten.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * _.flattenDeep([1, [2, [3, [4]], 5]]);
   * // => [1, 2, 3, 4, 5]
   */
  function flattenDeep(array) {
    var length = array == null ? 0 : array.length
    return length ? baseFlatten(array, INFINITY$4) : []
  }

  /**
   * Recursively flatten `array` up to `depth` times.
   *
   * @static
   * @memberOf _
   * @since 4.4.0
   * @category Array
   * @param {Array} array The array to flatten.
   * @param {number} [depth=1] The maximum recursion depth.
   * @returns {Array} Returns the new flattened array.
   * @example
   *
   * var array = [1, [2, [3, [4]], 5]];
   *
   * _.flattenDepth(array, 1);
   * // => [1, 2, [3, [4]], 5]
   *
   * _.flattenDepth(array, 2);
   * // => [1, 2, 3, [4], 5]
   */
  function flattenDepth(array, depth) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return []
    }
    depth = depth === undefined ? 1 : toInteger(depth)
    return baseFlatten(array, depth)
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_FLIP_FLAG$2 = 512

  /**
   * Creates a function that invokes `func` with arguments reversed.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Function
   * @param {Function} func The function to flip arguments for.
   * @returns {Function} Returns the new flipped function.
   * @example
   *
   * var flipped = _.flip(function() {
   *   return _.toArray(arguments);
   * });
   *
   * flipped('a', 'b', 'c', 'd');
   * // => ['d', 'c', 'b', 'a']
   */
  function flip(func) {
    return createWrap(func, WRAP_FLIP_FLAG$2)
  }

  /**
   * Computes `number` rounded down to `precision`.
   *
   * @static
   * @memberOf _
   * @since 3.10.0
   * @category Math
   * @param {number} number The number to round down.
   * @param {number} [precision=0] The precision to round down to.
   * @returns {number} Returns the rounded down number.
   * @example
   *
   * _.floor(4.006);
   * // => 4
   *
   * _.floor(0.046, 2);
   * // => 0.04
   *
   * _.floor(4060, -2);
   * // => 4000
   */
  var floor = createRound('floor')

  /** Error message constants. */
  var FUNC_ERROR_TEXT$7 = 'Expected a function'

  /** Used to compose bitmasks for function metadata. */
  var WRAP_CURRY_FLAG$6 = 8,
    WRAP_PARTIAL_FLAG$5 = 32,
    WRAP_ARY_FLAG$4 = 128,
    WRAP_REARG_FLAG$2 = 256

  /**
   * Creates a `_.flow` or `_.flowRight` function.
   *
   * @private
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new flow function.
   */
  function createFlow(fromRight) {
    return flatRest(function(funcs) {
      var length = funcs.length,
        index = length,
        prereq = LodashWrapper.prototype.thru

      if (fromRight) {
        funcs.reverse()
      }
      while (index--) {
        var func = funcs[index]
        if (typeof func != 'function') {
          throw new TypeError(FUNC_ERROR_TEXT$7)
        }
        if (prereq && !wrapper && getFuncName(func) == 'wrapper') {
          var wrapper = new LodashWrapper([], true)
        }
      }
      index = wrapper ? index : length
      while (++index < length) {
        func = funcs[index]

        var funcName = getFuncName(func),
          data = funcName == 'wrapper' ? getData(func) : undefined

        if (
          data &&
          isLaziable(data[0]) &&
          data[1] ==
            (WRAP_ARY_FLAG$4 |
              WRAP_CURRY_FLAG$6 |
              WRAP_PARTIAL_FLAG$5 |
              WRAP_REARG_FLAG$2) &&
          !data[4].length &&
          data[9] == 1
        ) {
          wrapper = wrapper[getFuncName(data[0])].apply(wrapper, data[3])
        } else {
          wrapper =
            func.length == 1 && isLaziable(func)
              ? wrapper[funcName]()
              : wrapper.thru(func)
        }
      }
      return function() {
        var args = arguments,
          value = args[0]

        if (wrapper && args.length == 1 && isArray(value)) {
          return wrapper.plant(value).value()
        }
        var index = 0,
          result = length ? funcs[index].apply(this, args) : value

        while (++index < length) {
          result = funcs[index].call(this, result)
        }
        return result
      }
    })
  }

  /**
   * Creates a function that returns the result of invoking the given functions
   * with the `this` binding of the created function, where each successive
   * invocation is supplied the return value of the previous.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Util
   * @param {...(Function|Function[])} [funcs] The functions to invoke.
   * @returns {Function} Returns the new composite function.
   * @see _.flowRight
   * @example
   *
   * function square(n) {
   *   return n * n;
   * }
   *
   * var addSquare = _.flow([_.add, square]);
   * addSquare(1, 2);
   * // => 9
   */
  var flow = createFlow()

  /**
   * This method is like `_.flow` except that it creates a function that
   * invokes the given functions from right to left.
   *
   * @static
   * @since 3.0.0
   * @memberOf _
   * @category Util
   * @param {...(Function|Function[])} [funcs] The functions to invoke.
   * @returns {Function} Returns the new composite function.
   * @see _.flow
   * @example
   *
   * function square(n) {
   *   return n * n;
   * }
   *
   * var addSquare = _.flowRight([square, _.add]);
   * addSquare(1, 2);
   * // => 9
   */
  var flowRight = createFlow(true)

  /**
   * Iterates over own and inherited enumerable string keyed properties of an
   * object and invokes `iteratee` for each property. The iteratee is invoked
   * with three arguments: (value, key, object). Iteratee functions may exit
   * iteration early by explicitly returning `false`.
   *
   * @static
   * @memberOf _
   * @since 0.3.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns `object`.
   * @see _.forInRight
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.forIn(new Foo, function(value, key) {
   *   console.log(key);
   * });
   * // => Logs 'a', 'b', then 'c' (iteration order is not guaranteed).
   */
  function forIn(object, iteratee) {
    return object == null
      ? object
      : baseFor(object, castFunction(iteratee), keysIn$1)
  }

  /**
   * This method is like `_.forIn` except that it iterates over properties of
   * `object` in the opposite order.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns `object`.
   * @see _.forIn
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.forInRight(new Foo, function(value, key) {
   *   console.log(key);
   * });
   * // => Logs 'c', 'b', then 'a' assuming `_.forIn` logs 'a', 'b', then 'c'.
   */
  function forInRight(object, iteratee) {
    return object == null
      ? object
      : baseForRight(object, castFunction(iteratee), keysIn$1)
  }

  /**
   * Iterates over own enumerable string keyed properties of an object and
   * invokes `iteratee` for each property. The iteratee is invoked with three
   * arguments: (value, key, object). Iteratee functions may exit iteration
   * early by explicitly returning `false`.
   *
   * @static
   * @memberOf _
   * @since 0.3.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns `object`.
   * @see _.forOwnRight
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.forOwn(new Foo, function(value, key) {
   *   console.log(key);
   * });
   * // => Logs 'a' then 'b' (iteration order is not guaranteed).
   */
  function forOwn(object, iteratee) {
    return object && baseForOwn(object, castFunction(iteratee))
  }

  /**
   * This method is like `_.forOwn` except that it iterates over properties of
   * `object` in the opposite order.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns `object`.
   * @see _.forOwn
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.forOwnRight(new Foo, function(value, key) {
   *   console.log(key);
   * });
   * // => Logs 'b' then 'a' assuming `_.forOwn` logs 'a' then 'b'.
   */
  function forOwnRight(object, iteratee) {
    return object && baseForOwnRight(object, castFunction(iteratee))
  }

  /**
   * The inverse of `_.toPairs`; this method returns an object composed
   * from key-value `pairs`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} pairs The key-value pairs.
   * @returns {Object} Returns the new object.
   * @example
   *
   * _.fromPairs([['a', 1], ['b', 2]]);
   * // => { 'a': 1, 'b': 2 }
   */
  function fromPairs(pairs) {
    var index = -1,
      length = pairs == null ? 0 : pairs.length,
      result = {}

    while (++index < length) {
      var pair = pairs[index]
      result[pair[0]] = pair[1]
    }
    return result
  }

  /**
   * The base implementation of `_.functions` which creates an array of
   * `object` function property names filtered from `props`.
   *
   * @private
   * @param {Object} object The object to inspect.
   * @param {Array} props The property names to filter.
   * @returns {Array} Returns the function names.
   */
  function baseFunctions(object, props) {
    return arrayFilter(props, function(key) {
      return isFunction(object[key])
    })
  }

  /**
   * Creates an array of function property names from own enumerable properties
   * of `object`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The object to inspect.
   * @returns {Array} Returns the function names.
   * @see _.functionsIn
   * @example
   *
   * function Foo() {
   *   this.a = _.constant('a');
   *   this.b = _.constant('b');
   * }
   *
   * Foo.prototype.c = _.constant('c');
   *
   * _.functions(new Foo);
   * // => ['a', 'b']
   */
  function functions(object) {
    return object == null ? [] : baseFunctions(object, keys(object))
  }

  /**
   * Creates an array of function property names from own and inherited
   * enumerable properties of `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The object to inspect.
   * @returns {Array} Returns the function names.
   * @see _.functions
   * @example
   *
   * function Foo() {
   *   this.a = _.constant('a');
   *   this.b = _.constant('b');
   * }
   *
   * Foo.prototype.c = _.constant('c');
   *
   * _.functionsIn(new Foo);
   * // => ['a', 'b', 'c']
   */
  function functionsIn(object) {
    return object == null ? [] : baseFunctions(object, keysIn$1(object))
  }

  /** Used for built-in method references. */
  var objectProto$l = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$j = objectProto$l.hasOwnProperty

  /**
   * Creates an object composed of keys generated from the results of running
   * each element of `collection` thru `iteratee`. The order of grouped values
   * is determined by the order they occur in `collection`. The corresponding
   * value of each key is an array of elements responsible for generating the
   * key. The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee to transform keys.
   * @returns {Object} Returns the composed aggregate object.
   * @example
   *
   * _.groupBy([6.1, 4.2, 6.3], Math.floor);
   * // => { '4': [4.2], '6': [6.1, 6.3] }
   *
   * // The `_.property` iteratee shorthand.
   * _.groupBy(['one', 'two', 'three'], 'length');
   * // => { '3': ['one', 'two'], '5': ['three'] }
   */
  var groupBy = createAggregator(function(result, value, key) {
    if (hasOwnProperty$j.call(result, key)) {
      result[key].push(value)
    } else {
      baseAssignValue(result, key, [value])
    }
  })

  /**
   * The base implementation of `_.gt` which doesn't coerce arguments.
   *
   * @private
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if `value` is greater than `other`,
   *  else `false`.
   */
  function baseGt(value, other) {
    return value > other
  }

  /**
   * Creates a function that performs a relational operation on two values.
   *
   * @private
   * @param {Function} operator The function to perform the operation.
   * @returns {Function} Returns the new relational operation function.
   */
  function createRelationalOperation(operator) {
    return function(value, other) {
      if (!(typeof value == 'string' && typeof other == 'string')) {
        value = toNumber(value)
        other = toNumber(other)
      }
      return operator(value, other)
    }
  }

  /**
   * Checks if `value` is greater than `other`.
   *
   * @static
   * @memberOf _
   * @since 3.9.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if `value` is greater than `other`,
   *  else `false`.
   * @see _.lt
   * @example
   *
   * _.gt(3, 1);
   * // => true
   *
   * _.gt(3, 3);
   * // => false
   *
   * _.gt(1, 3);
   * // => false
   */
  var gt$1 = createRelationalOperation(baseGt)

  /**
   * Checks if `value` is greater than or equal to `other`.
   *
   * @static
   * @memberOf _
   * @since 3.9.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if `value` is greater than or equal to
   *  `other`, else `false`.
   * @see _.lte
   * @example
   *
   * _.gte(3, 1);
   * // => true
   *
   * _.gte(3, 3);
   * // => true
   *
   * _.gte(1, 3);
   * // => false
   */
  var gte$1 = createRelationalOperation(function(value, other) {
    return value >= other
  })

  /** Used for built-in method references. */
  var objectProto$m = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$k = objectProto$m.hasOwnProperty

  /**
   * The base implementation of `_.has` without support for deep paths.
   *
   * @private
   * @param {Object} [object] The object to query.
   * @param {Array|string} key The key to check.
   * @returns {boolean} Returns `true` if `key` exists, else `false`.
   */
  function baseHas(object, key) {
    return object != null && hasOwnProperty$k.call(object, key)
  }

  /**
   * Checks if `path` is a direct property of `object`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path to check.
   * @returns {boolean} Returns `true` if `path` exists, else `false`.
   * @example
   *
   * var object = { 'a': { 'b': 2 } };
   * var other = _.create({ 'a': _.create({ 'b': 2 }) });
   *
   * _.has(object, 'a');
   * // => true
   *
   * _.has(object, 'a.b');
   * // => true
   *
   * _.has(object, ['a', 'b']);
   * // => true
   *
   * _.has(other, 'a');
   * // => false
   */
  function has$2(object, path) {
    return object != null && hasPath(object, path, baseHas)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$8 = Math.max,
    nativeMin$5 = Math.min

  /**
   * The base implementation of `_.inRange` which doesn't coerce arguments.
   *
   * @private
   * @param {number} number The number to check.
   * @param {number} start The start of the range.
   * @param {number} end The end of the range.
   * @returns {boolean} Returns `true` if `number` is in the range, else `false`.
   */
  function baseInRange(number, start, end) {
    return number >= nativeMin$5(start, end) && number < nativeMax$8(start, end)
  }

  /**
   * Checks if `n` is between `start` and up to, but not including, `end`. If
   * `end` is not specified, it's set to `start` with `start` then set to `0`.
   * If `start` is greater than `end` the params are swapped to support
   * negative ranges.
   *
   * @static
   * @memberOf _
   * @since 3.3.0
   * @category Number
   * @param {number} number The number to check.
   * @param {number} [start=0] The start of the range.
   * @param {number} end The end of the range.
   * @returns {boolean} Returns `true` if `number` is in the range, else `false`.
   * @see _.range, _.rangeRight
   * @example
   *
   * _.inRange(3, 2, 4);
   * // => true
   *
   * _.inRange(4, 8);
   * // => true
   *
   * _.inRange(4, 2);
   * // => false
   *
   * _.inRange(2, 2);
   * // => false
   *
   * _.inRange(1.2, 2);
   * // => true
   *
   * _.inRange(5.2, 4);
   * // => false
   *
   * _.inRange(-3, -2, -6);
   * // => true
   */
  function inRange$1(number, start, end) {
    start = toFinite(start)
    if (end === undefined) {
      end = start
      start = 0
    } else {
      end = toFinite(end)
    }
    number = toNumber(number)
    return baseInRange(number, start, end)
  }

  /** `Object#toString` result references. */
  var stringTag$4 = '[object String]'

  /**
   * Checks if `value` is classified as a `String` primitive or object.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a string, else `false`.
   * @example
   *
   * _.isString('abc');
   * // => true
   *
   * _.isString(1);
   * // => false
   */
  function isString(value) {
    return (
      typeof value == 'string' ||
      (!isArray(value) &&
        isObjectLike(value) &&
        baseGetTag(value) == stringTag$4)
    )
  }

  /**
   * The base implementation of `_.values` and `_.valuesIn` which creates an
   * array of `object` property values corresponding to the property names
   * of `props`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array} props The property names to get values for.
   * @returns {Object} Returns the array of property values.
   */
  function baseValues(object, props) {
    return arrayMap(props, function(key) {
      return object[key]
    })
  }

  /**
   * Creates an array of the own enumerable string keyed property values of `object`.
   *
   * **Note:** Non-object values are coerced to objects.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property values.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.values(new Foo);
   * // => [1, 2] (iteration order is not guaranteed)
   *
   * _.values('hi');
   * // => ['h', 'i']
   */
  function values(object) {
    return object == null ? [] : baseValues(object, keys(object))
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$9 = Math.max

  /**
   * Checks if `value` is in `collection`. If `collection` is a string, it's
   * checked for a substring of `value`, otherwise
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * is used for equality comparisons. If `fromIndex` is negative, it's used as
   * the offset from the end of `collection`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object|string} collection The collection to inspect.
   * @param {*} value The value to search for.
   * @param {number} [fromIndex=0] The index to search from.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.reduce`.
   * @returns {boolean} Returns `true` if `value` is found, else `false`.
   * @example
   *
   * _.includes([1, 2, 3], 1);
   * // => true
   *
   * _.includes([1, 2, 3], 1, 2);
   * // => false
   *
   * _.includes({ 'a': 1, 'b': 2 }, 1);
   * // => true
   *
   * _.includes('abcd', 'bc');
   * // => true
   */
  function includes(collection, value, fromIndex, guard) {
    collection = isArrayLike(collection) ? collection : values(collection)
    fromIndex = fromIndex && !guard ? toInteger(fromIndex) : 0

    var length = collection.length
    if (fromIndex < 0) {
      fromIndex = nativeMax$9(length + fromIndex, 0)
    }
    return isString(collection)
      ? fromIndex <= length && collection.indexOf(value, fromIndex) > -1
      : !!length && baseIndexOf(collection, value, fromIndex) > -1
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$a = Math.max

  /**
   * Gets the index at which the first occurrence of `value` is found in `array`
   * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons. If `fromIndex` is negative, it's used as the
   * offset from the end of `array`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} [fromIndex=0] The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   * @example
   *
   * _.indexOf([1, 2, 1, 2], 2);
   * // => 1
   *
   * // Search from the `fromIndex`.
   * _.indexOf([1, 2, 1, 2], 2, 2);
   * // => 3
   */
  function indexOf(array, value, fromIndex) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return -1
    }
    var index = fromIndex == null ? 0 : toInteger(fromIndex)
    if (index < 0) {
      index = nativeMax$a(length + index, 0)
    }
    return baseIndexOf(array, value, index)
  }

  /**
   * Gets all but the last element of `array`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to query.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * _.initial([1, 2, 3]);
   * // => [1, 2]
   */
  function initial(array) {
    var length = array == null ? 0 : array.length
    return length ? baseSlice(array, 0, -1) : []
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin$6 = Math.min

  /**
   * The base implementation of methods like `_.intersection`, without support
   * for iteratee shorthands, that accepts an array of arrays to inspect.
   *
   * @private
   * @param {Array} arrays The arrays to inspect.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of shared values.
   */
  function baseIntersection(arrays, iteratee, comparator) {
    var includes = comparator ? arrayIncludesWith : arrayIncludes,
      length = arrays[0].length,
      othLength = arrays.length,
      othIndex = othLength,
      caches = Array(othLength),
      maxLength = Infinity,
      result = []

    while (othIndex--) {
      var array = arrays[othIndex]
      if (othIndex && iteratee) {
        array = arrayMap(array, baseUnary(iteratee))
      }
      maxLength = nativeMin$6(array.length, maxLength)
      caches[othIndex] =
        !comparator && (iteratee || (length >= 120 && array.length >= 120))
          ? new SetCache(othIndex && array)
          : undefined
    }
    array = arrays[0]

    var index = -1,
      seen = caches[0]

    outer: while (++index < length && result.length < maxLength) {
      var value = array[index],
        computed = iteratee ? iteratee(value) : value

      value = comparator || value !== 0 ? value : 0
      if (
        !(seen
          ? cacheHas(seen, computed)
          : includes(result, computed, comparator))
      ) {
        othIndex = othLength
        while (--othIndex) {
          var cache = caches[othIndex]
          if (
            !(cache
              ? cacheHas(cache, computed)
              : includes(arrays[othIndex], computed, comparator))
          ) {
            continue outer
          }
        }
        if (seen) {
          seen.push(computed)
        }
        result.push(value)
      }
    }
    return result
  }

  /**
   * Casts `value` to an empty array if it's not an array like object.
   *
   * @private
   * @param {*} value The value to inspect.
   * @returns {Array|Object} Returns the cast array-like object.
   */
  function castArrayLikeObject(value) {
    return isArrayLikeObject(value) ? value : []
  }

  /**
   * Creates an array of unique values that are included in all given arrays
   * using [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons. The order and references of result values are
   * determined by the first array.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @returns {Array} Returns the new array of intersecting values.
   * @example
   *
   * _.intersection([2, 1], [2, 3]);
   * // => [2]
   */
  var intersection = baseRest(function(arrays) {
    var mapped = arrayMap(arrays, castArrayLikeObject)
    return mapped.length && mapped[0] === arrays[0]
      ? baseIntersection(mapped)
      : []
  })

  /**
   * This method is like `_.intersection` except that it accepts `iteratee`
   * which is invoked for each element of each `arrays` to generate the criterion
   * by which they're compared. The order and references of result values are
   * determined by the first array. The iteratee is invoked with one argument:
   * (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Array} Returns the new array of intersecting values.
   * @example
   *
   * _.intersectionBy([2.1, 1.2], [2.3, 3.4], Math.floor);
   * // => [2.1]
   *
   * // The `_.property` iteratee shorthand.
   * _.intersectionBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
   * // => [{ 'x': 1 }]
   */
  var intersectionBy = baseRest(function(arrays) {
    var iteratee = last(arrays),
      mapped = arrayMap(arrays, castArrayLikeObject)

    if (iteratee === last(mapped)) {
      iteratee = undefined
    } else {
      mapped.pop()
    }
    return mapped.length && mapped[0] === arrays[0]
      ? baseIntersection(mapped, baseIteratee(iteratee))
      : []
  })

  /**
   * This method is like `_.intersection` except that it accepts `comparator`
   * which is invoked to compare elements of `arrays`. The order and references
   * of result values are determined by the first array. The comparator is
   * invoked with two arguments: (arrVal, othVal).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of intersecting values.
   * @example
   *
   * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
   * var others = [{ 'x': 1, 'y': 1 }, { 'x': 1, 'y': 2 }];
   *
   * _.intersectionWith(objects, others, _.isEqual);
   * // => [{ 'x': 1, 'y': 2 }]
   */
  var intersectionWith = baseRest(function(arrays) {
    var comparator = last(arrays),
      mapped = arrayMap(arrays, castArrayLikeObject)

    comparator = typeof comparator == 'function' ? comparator : undefined
    if (comparator) {
      mapped.pop()
    }
    return mapped.length && mapped[0] === arrays[0]
      ? baseIntersection(mapped, undefined, comparator)
      : []
  })

  /**
   * The base implementation of `_.invert` and `_.invertBy` which inverts
   * `object` with values transformed by `iteratee` and set by `setter`.
   *
   * @private
   * @param {Object} object The object to iterate over.
   * @param {Function} setter The function to set `accumulator` values.
   * @param {Function} iteratee The iteratee to transform values.
   * @param {Object} accumulator The initial inverted object.
   * @returns {Function} Returns `accumulator`.
   */
  function baseInverter(object, setter, iteratee, accumulator) {
    baseForOwn(object, function(value, key, object) {
      setter(accumulator, iteratee(value), key, object)
    })
    return accumulator
  }

  /**
   * Creates a function like `_.invertBy`.
   *
   * @private
   * @param {Function} setter The function to set accumulator values.
   * @param {Function} toIteratee The function to resolve iteratees.
   * @returns {Function} Returns the new inverter function.
   */
  function createInverter(setter, toIteratee) {
    return function(object, iteratee) {
      return baseInverter(object, setter, toIteratee(iteratee), {})
    }
  }

  /** Used for built-in method references. */
  var objectProto$n = Object.prototype

  /**
   * Used to resolve the
   * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
   * of values.
   */
  var nativeObjectToString$2 = objectProto$n.toString

  /**
   * Creates an object composed of the inverted keys and values of `object`.
   * If `object` contains duplicate values, subsequent values overwrite
   * property assignments of previous values.
   *
   * @static
   * @memberOf _
   * @since 0.7.0
   * @category Object
   * @param {Object} object The object to invert.
   * @returns {Object} Returns the new inverted object.
   * @example
   *
   * var object = { 'a': 1, 'b': 2, 'c': 1 };
   *
   * _.invert(object);
   * // => { '1': 'c', '2': 'b' }
   */
  var invert = createInverter(function(result, value, key) {
    if (value != null && typeof value.toString != 'function') {
      value = nativeObjectToString$2.call(value)
    }

    result[value] = key
  }, constant(identity))

  /** Used for built-in method references. */
  var objectProto$o = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$l = objectProto$o.hasOwnProperty

  /**
   * Used to resolve the
   * [`toStringTag`](http://ecma-international.org/ecma-262/7.0/#sec-object.prototype.tostring)
   * of values.
   */
  var nativeObjectToString$3 = objectProto$o.toString

  /**
   * This method is like `_.invert` except that the inverted object is generated
   * from the results of running each element of `object` thru `iteratee`. The
   * corresponding inverted value of each inverted key is an array of keys
   * responsible for generating the inverted value. The iteratee is invoked
   * with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.1.0
   * @category Object
   * @param {Object} object The object to invert.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Object} Returns the new inverted object.
   * @example
   *
   * var object = { 'a': 1, 'b': 2, 'c': 1 };
   *
   * _.invertBy(object);
   * // => { '1': ['a', 'c'], '2': ['b'] }
   *
   * _.invertBy(object, function(value) {
   *   return 'group' + value;
   * });
   * // => { 'group1': ['a', 'c'], 'group2': ['b'] }
   */
  var invertBy = createInverter(function(result, value, key) {
    if (value != null && typeof value.toString != 'function') {
      value = nativeObjectToString$3.call(value)
    }

    if (hasOwnProperty$l.call(result, value)) {
      result[value].push(key)
    } else {
      result[value] = [key]
    }
  }, baseIteratee)

  /**
   * Gets the parent value at `path` of `object`.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array} path The path to get the parent value of.
   * @returns {*} Returns the parent value.
   */
  function parent(object, path) {
    return path.length < 2 ? object : baseGet(object, baseSlice(path, 0, -1))
  }

  /**
   * The base implementation of `_.invoke` without support for individual
   * method arguments.
   *
   * @private
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the method to invoke.
   * @param {Array} args The arguments to invoke the method with.
   * @returns {*} Returns the result of the invoked method.
   */
  function baseInvoke(object, path, args) {
    path = castPath(path, object)
    object = parent(object, path)
    var func = object == null ? object : object[toKey(last(path))]
    return func == null ? undefined : apply(func, object, args)
  }

  /**
   * Invokes the method at `path` of `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the method to invoke.
   * @param {...*} [args] The arguments to invoke the method with.
   * @returns {*} Returns the result of the invoked method.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': [1, 2, 3, 4] } }] };
   *
   * _.invoke(object, 'a[0].b.c.slice', 1, 3);
   * // => [2, 3]
   */
  var invoke = baseRest(baseInvoke)

  /**
   * Invokes the method at `path` of each element in `collection`, returning
   * an array of the results of each invoked method. Any additional arguments
   * are provided to each invoked method. If `path` is a function, it's invoked
   * for, and `this` bound to, each element in `collection`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Array|Function|string} path The path of the method to invoke or
   *  the function invoked per iteration.
   * @param {...*} [args] The arguments to invoke each method with.
   * @returns {Array} Returns the array of results.
   * @example
   *
   * _.invokeMap([[5, 1, 7], [3, 2, 1]], 'sort');
   * // => [[1, 5, 7], [1, 2, 3]]
   *
   * _.invokeMap([123, 456], String.prototype.split, '');
   * // => [['1', '2', '3'], ['4', '5', '6']]
   */
  var invokeMap = baseRest(function(collection, path, args) {
    var index = -1,
      isFunc = typeof path == 'function',
      result = isArrayLike(collection) ? Array(collection.length) : []

    baseEach(collection, function(value) {
      result[++index] = isFunc
        ? apply(path, value, args)
        : baseInvoke(value, path, args)
    })
    return result
  })

  var arrayBufferTag$4 = '[object ArrayBuffer]'

  /**
   * The base implementation of `_.isArrayBuffer` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an array buffer, else `false`.
   */
  function baseIsArrayBuffer(value) {
    return isObjectLike(value) && baseGetTag(value) == arrayBufferTag$4
  }

  /* Node.js helper references. */
  var nodeIsArrayBuffer = nodeUtil && nodeUtil.isArrayBuffer

  /**
   * Checks if `value` is classified as an `ArrayBuffer` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an array buffer, else `false`.
   * @example
   *
   * _.isArrayBuffer(new ArrayBuffer(2));
   * // => true
   *
   * _.isArrayBuffer(new Array(2));
   * // => false
   */
  var isArrayBuffer = nodeIsArrayBuffer
    ? baseUnary(nodeIsArrayBuffer)
    : baseIsArrayBuffer

  /** `Object#toString` result references. */
  var boolTag$4 = '[object Boolean]'

  /**
   * Checks if `value` is classified as a boolean primitive or object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a boolean, else `false`.
   * @example
   *
   * _.isBoolean(false);
   * // => true
   *
   * _.isBoolean(null);
   * // => false
   */
  function isBoolean(value) {
    return (
      value === true ||
      value === false ||
      (isObjectLike(value) && baseGetTag(value) == boolTag$4)
    )
  }

  /** `Object#toString` result references. */
  var dateTag$4 = '[object Date]'

  /**
   * The base implementation of `_.isDate` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a date object, else `false`.
   */
  function baseIsDate(value) {
    return isObjectLike(value) && baseGetTag(value) == dateTag$4
  }

  /* Node.js helper references. */
  var nodeIsDate = nodeUtil && nodeUtil.isDate

  /**
   * Checks if `value` is classified as a `Date` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a date object, else `false`.
   * @example
   *
   * _.isDate(new Date);
   * // => true
   *
   * _.isDate('Mon April 23 2012');
   * // => false
   */
  var isDate = nodeIsDate ? baseUnary(nodeIsDate) : baseIsDate

  /**
   * Checks if `value` is likely a DOM element.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a DOM element, else `false`.
   * @example
   *
   * _.isElement(document.body);
   * // => true
   *
   * _.isElement('<body>');
   * // => false
   */
  function isElement(value) {
    return isObjectLike(value) && value.nodeType === 1 && !isPlainObject(value)
  }

  /** `Object#toString` result references. */
  var mapTag$7 = '[object Map]',
    setTag$7 = '[object Set]'

  /** Used for built-in method references. */
  var objectProto$p = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$m = objectProto$p.hasOwnProperty

  /**
   * Checks if `value` is an empty object, collection, map, or set.
   *
   * Objects are considered empty if they have no own enumerable string keyed
   * properties.
   *
   * Array-like values such as `arguments` objects, arrays, buffers, strings, or
   * jQuery-like collections are considered empty if they have a `length` of `0`.
   * Similarly, maps and sets are considered empty if they have a `size` of `0`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is empty, else `false`.
   * @example
   *
   * _.isEmpty(null);
   * // => true
   *
   * _.isEmpty(true);
   * // => true
   *
   * _.isEmpty(1);
   * // => true
   *
   * _.isEmpty([1, 2, 3]);
   * // => false
   *
   * _.isEmpty({ 'a': 1 });
   * // => false
   */
  function isEmpty(value) {
    if (value == null) {
      return true
    }
    if (
      isArrayLike(value) &&
      (isArray(value) ||
        typeof value == 'string' ||
        typeof value.splice == 'function' ||
        isBuffer(value) ||
        isTypedArray(value) ||
        isArguments(value))
    ) {
      return !value.length
    }
    var tag = getTag$1(value)
    if (tag == mapTag$7 || tag == setTag$7) {
      return !value.size
    }
    if (isPrototype(value)) {
      return !baseKeys(value).length
    }
    for (var key in value) {
      if (hasOwnProperty$m.call(value, key)) {
        return false
      }
    }
    return true
  }

  /**
   * Performs a deep comparison between two values to determine if they are
   * equivalent.
   *
   * **Note:** This method supports comparing arrays, array buffers, booleans,
   * date objects, error objects, maps, numbers, `Object` objects, regexes,
   * sets, strings, symbols, and typed arrays. `Object` objects are compared
   * by their own, not inherited, enumerable properties. Functions and DOM
   * nodes are compared by strict equality, i.e. `===`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
   * @example
   *
   * var object = { 'a': 1 };
   * var other = { 'a': 1 };
   *
   * _.isEqual(object, other);
   * // => true
   *
   * object === other;
   * // => false
   */
  function isEqual(value, other) {
    return baseIsEqual(value, other)
  }

  /**
   * This method is like `_.isEqual` except that it accepts `customizer` which
   * is invoked to compare values. If `customizer` returns `undefined`, comparisons
   * are handled by the method instead. The `customizer` is invoked with up to
   * six arguments: (objValue, othValue [, index|key, object, other, stack]).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @param {Function} [customizer] The function to customize comparisons.
   * @returns {boolean} Returns `true` if the values are equivalent, else `false`.
   * @example
   *
   * function isGreeting(value) {
   *   return /^h(?:i|ello)$/.test(value);
   * }
   *
   * function customizer(objValue, othValue) {
   *   if (isGreeting(objValue) && isGreeting(othValue)) {
   *     return true;
   *   }
   * }
   *
   * var array = ['hello', 'goodbye'];
   * var other = ['hi', 'goodbye'];
   *
   * _.isEqualWith(array, other, customizer);
   * // => true
   */
  function isEqualWith(value, other, customizer) {
    customizer = typeof customizer == 'function' ? customizer : undefined
    var result = customizer ? customizer(value, other) : undefined
    return result === undefined
      ? baseIsEqual(value, other, undefined, customizer)
      : !!result
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeIsFinite$1 = root.isFinite

  /**
   * Checks if `value` is a finite primitive number.
   *
   * **Note:** This method is based on
   * [`Number.isFinite`](https://mdn.io/Number/isFinite).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a finite number, else `false`.
   * @example
   *
   * _.isFinite(3);
   * // => true
   *
   * _.isFinite(Number.MIN_VALUE);
   * // => true
   *
   * _.isFinite(Infinity);
   * // => false
   *
   * _.isFinite('3');
   * // => false
   */
  function isFinite$1(value) {
    return typeof value == 'number' && nativeIsFinite$1(value)
  }

  /**
   * Checks if `value` is an integer.
   *
   * **Note:** This method is based on
   * [`Number.isInteger`](https://mdn.io/Number/isInteger).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is an integer, else `false`.
   * @example
   *
   * _.isInteger(3);
   * // => true
   *
   * _.isInteger(Number.MIN_VALUE);
   * // => false
   *
   * _.isInteger(Infinity);
   * // => false
   *
   * _.isInteger('3');
   * // => false
   */
  function isInteger(value) {
    return typeof value == 'number' && value == toInteger(value)
  }

  /**
   * Performs a partial deep comparison between `object` and `source` to
   * determine if `object` contains equivalent property values.
   *
   * **Note:** This method is equivalent to `_.matches` when `source` is
   * partially applied.
   *
   * Partial comparisons will match empty array and empty object `source`
   * values against any array or object value, respectively. See `_.isEqual`
   * for a list of supported value comparisons.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Lang
   * @param {Object} object The object to inspect.
   * @param {Object} source The object of property values to match.
   * @returns {boolean} Returns `true` if `object` is a match, else `false`.
   * @example
   *
   * var object = { 'a': 1, 'b': 2 };
   *
   * _.isMatch(object, { 'b': 2 });
   * // => true
   *
   * _.isMatch(object, { 'b': 1 });
   * // => false
   */
  function isMatch(object, source) {
    return (
      object === source || baseIsMatch(object, source, getMatchData(source))
    )
  }

  /**
   * This method is like `_.isMatch` except that it accepts `customizer` which
   * is invoked to compare values. If `customizer` returns `undefined`, comparisons
   * are handled by the method instead. The `customizer` is invoked with five
   * arguments: (objValue, srcValue, index|key, object, source).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {Object} object The object to inspect.
   * @param {Object} source The object of property values to match.
   * @param {Function} [customizer] The function to customize comparisons.
   * @returns {boolean} Returns `true` if `object` is a match, else `false`.
   * @example
   *
   * function isGreeting(value) {
   *   return /^h(?:i|ello)$/.test(value);
   * }
   *
   * function customizer(objValue, srcValue) {
   *   if (isGreeting(objValue) && isGreeting(srcValue)) {
   *     return true;
   *   }
   * }
   *
   * var object = { 'greeting': 'hello' };
   * var source = { 'greeting': 'hi' };
   *
   * _.isMatchWith(object, source, customizer);
   * // => true
   */
  function isMatchWith(object, source, customizer) {
    customizer = typeof customizer == 'function' ? customizer : undefined
    return baseIsMatch(object, source, getMatchData(source), customizer)
  }

  /** `Object#toString` result references. */
  var numberTag$4 = '[object Number]'

  /**
   * Checks if `value` is classified as a `Number` primitive or object.
   *
   * **Note:** To exclude `Infinity`, `-Infinity`, and `NaN`, which are
   * classified as numbers, use the `_.isFinite` method.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a number, else `false`.
   * @example
   *
   * _.isNumber(3);
   * // => true
   *
   * _.isNumber(Number.MIN_VALUE);
   * // => true
   *
   * _.isNumber(Infinity);
   * // => true
   *
   * _.isNumber('3');
   * // => false
   */
  function isNumber(value) {
    return (
      typeof value == 'number' ||
      (isObjectLike(value) && baseGetTag(value) == numberTag$4)
    )
  }

  /**
   * Checks if `value` is `NaN`.
   *
   * **Note:** This method is based on
   * [`Number.isNaN`](https://mdn.io/Number/isNaN) and is not the same as
   * global [`isNaN`](https://mdn.io/isNaN) which returns `true` for
   * `undefined` and other non-number values.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is `NaN`, else `false`.
   * @example
   *
   * _.isNaN(NaN);
   * // => true
   *
   * _.isNaN(new Number(NaN));
   * // => true
   *
   * isNaN(undefined);
   * // => true
   *
   * _.isNaN(undefined);
   * // => false
   */
  function isNaN$1(value) {
    // An `NaN` primitive is the only value that is not equal to itself.
    // Perform the `toStringTag` check first to avoid errors with some
    // ActiveX objects in IE.
    return isNumber(value) && value != +value
  }

  /**
   * Checks if `func` is capable of being masked.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `func` is maskable, else `false`.
   */
  var isMaskable = coreJsData ? isFunction : stubFalse

  /** Error message constants. */
  var CORE_ERROR_TEXT =
    'Unsupported core-js use. Try https://npms.io/search?q=ponyfill.'

  /**
   * Checks if `value` is a pristine native function.
   *
   * **Note:** This method can't reliably detect native functions in the presence
   * of the core-js package because core-js circumvents this kind of detection.
   * Despite multiple requests, the core-js maintainer has made it clear: any
   * attempt to fix the detection will be obstructed. As a result, we're left
   * with little choice but to throw an error. Unfortunately, this also affects
   * packages, like [babel-polyfill](https://www.npmjs.com/package/babel-polyfill),
   * which rely on core-js.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a native function,
   *  else `false`.
   * @example
   *
   * _.isNative(Array.prototype.push);
   * // => true
   *
   * _.isNative(_);
   * // => false
   */
  function isNative(value) {
    if (isMaskable(value)) {
      throw new Error(CORE_ERROR_TEXT)
    }
    return baseIsNative(value)
  }

  /**
   * Checks if `value` is `null` or `undefined`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is nullish, else `false`.
   * @example
   *
   * _.isNil(null);
   * // => true
   *
   * _.isNil(void 0);
   * // => true
   *
   * _.isNil(NaN);
   * // => false
   */
  function isNil(value) {
    return value == null
  }

  /**
   * Checks if `value` is `null`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is `null`, else `false`.
   * @example
   *
   * _.isNull(null);
   * // => true
   *
   * _.isNull(void 0);
   * // => false
   */
  function isNull(value) {
    return value === null
  }

  /** `Object#toString` result references. */
  var regexpTag$4 = '[object RegExp]'

  /**
   * The base implementation of `_.isRegExp` without Node.js optimizations.
   *
   * @private
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a regexp, else `false`.
   */
  function baseIsRegExp(value) {
    return isObjectLike(value) && baseGetTag(value) == regexpTag$4
  }

  /* Node.js helper references. */
  var nodeIsRegExp = nodeUtil && nodeUtil.isRegExp

  /**
   * Checks if `value` is classified as a `RegExp` object.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a regexp, else `false`.
   * @example
   *
   * _.isRegExp(/abc/);
   * // => true
   *
   * _.isRegExp('/abc/');
   * // => false
   */
  var isRegExp = nodeIsRegExp ? baseUnary(nodeIsRegExp) : baseIsRegExp

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER$2 = 9007199254740991

  /**
   * Checks if `value` is a safe integer. An integer is safe if it's an IEEE-754
   * double precision number which isn't the result of a rounded unsafe integer.
   *
   * **Note:** This method is based on
   * [`Number.isSafeInteger`](https://mdn.io/Number/isSafeInteger).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a safe integer, else `false`.
   * @example
   *
   * _.isSafeInteger(3);
   * // => true
   *
   * _.isSafeInteger(Number.MIN_VALUE);
   * // => false
   *
   * _.isSafeInteger(Infinity);
   * // => false
   *
   * _.isSafeInteger('3');
   * // => false
   */
  function isSafeInteger(value) {
    return (
      isInteger(value) &&
      value >= -MAX_SAFE_INTEGER$2 &&
      value <= MAX_SAFE_INTEGER$2
    )
  }

  /**
   * Checks if `value` is `undefined`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is `undefined`, else `false`.
   * @example
   *
   * _.isUndefined(void 0);
   * // => true
   *
   * _.isUndefined(null);
   * // => false
   */
  function isUndefined(value) {
    return value === undefined
  }

  /** `Object#toString` result references. */
  var weakMapTag$3 = '[object WeakMap]'

  /**
   * Checks if `value` is classified as a `WeakMap` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a weak map, else `false`.
   * @example
   *
   * _.isWeakMap(new WeakMap);
   * // => true
   *
   * _.isWeakMap(new Map);
   * // => false
   */
  function isWeakMap(value) {
    return isObjectLike(value) && getTag$1(value) == weakMapTag$3
  }

  /** `Object#toString` result references. */
  var weakSetTag = '[object WeakSet]'

  /**
   * Checks if `value` is classified as a `WeakSet` object.
   *
   * @static
   * @memberOf _
   * @since 4.3.0
   * @category Lang
   * @param {*} value The value to check.
   * @returns {boolean} Returns `true` if `value` is a weak set, else `false`.
   * @example
   *
   * _.isWeakSet(new WeakSet);
   * // => true
   *
   * _.isWeakSet(new Set);
   * // => false
   */
  function isWeakSet(value) {
    return isObjectLike(value) && baseGetTag(value) == weakSetTag
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$4 = 1

  /**
   * Creates a function that invokes `func` with the arguments of the created
   * function. If `func` is a property name, the created function returns the
   * property value for a given element. If `func` is an array or object, the
   * created function returns `true` for elements that contain the equivalent
   * source properties, otherwise it returns `false`.
   *
   * @static
   * @since 4.0.0
   * @memberOf _
   * @category Util
   * @param {*} [func=_.identity] The value to convert to a callback.
   * @returns {Function} Returns the callback.
   * @example
   *
   * var users = [
   *   { 'user': 'barney', 'age': 36, 'active': true },
   *   { 'user': 'fred',   'age': 40, 'active': false }
   * ];
   *
   * // The `_.matches` iteratee shorthand.
   * _.filter(users, _.iteratee({ 'user': 'barney', 'active': true }));
   * // => [{ 'user': 'barney', 'age': 36, 'active': true }]
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.filter(users, _.iteratee(['user', 'fred']));
   * // => [{ 'user': 'fred', 'age': 40 }]
   *
   * // The `_.property` iteratee shorthand.
   * _.map(users, _.iteratee('user'));
   * // => ['barney', 'fred']
   *
   * // Create custom iteratee shorthands.
   * _.iteratee = _.wrap(_.iteratee, function(iteratee, func) {
   *   return !_.isRegExp(func) ? iteratee(func) : function(string) {
   *     return func.test(string);
   *   };
   * });
   *
   * _.filter(['abc', 'def'], /ef/);
   * // => ['def']
   */
  function iteratee(func) {
    return baseIteratee(
      typeof func == 'function' ? func : baseClone(func, CLONE_DEEP_FLAG$4)
    )
  }

  /** Used for built-in method references. */
  var arrayProto$1 = Array.prototype

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeJoin = arrayProto$1.join

  /**
   * Converts all elements in `array` into a string separated by `separator`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to convert.
   * @param {string} [separator=','] The element separator.
   * @returns {string} Returns the joined string.
   * @example
   *
   * _.join(['a', 'b', 'c'], '~');
   * // => 'a~b~c'
   */
  function join(array, separator) {
    return array == null ? '' : nativeJoin.call(array, separator)
  }

  /**
   * Converts `string` to
   * [kebab case](https://en.wikipedia.org/wiki/Letter_case#Special_case_styles).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the kebab cased string.
   * @example
   *
   * _.kebabCase('Foo Bar');
   * // => 'foo-bar'
   *
   * _.kebabCase('fooBar');
   * // => 'foo-bar'
   *
   * _.kebabCase('__FOO_BAR__');
   * // => 'foo-bar'
   */
  var kebabCase = createCompounder(function(result, word, index) {
    return result + (index ? '-' : '') + word.toLowerCase()
  })

  /**
   * Creates an object composed of keys generated from the results of running
   * each element of `collection` thru `iteratee`. The corresponding value of
   * each key is the last element responsible for generating the key. The
   * iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee to transform keys.
   * @returns {Object} Returns the composed aggregate object.
   * @example
   *
   * var array = [
   *   { 'dir': 'left', 'code': 97 },
   *   { 'dir': 'right', 'code': 100 }
   * ];
   *
   * _.keyBy(array, function(o) {
   *   return String.fromCharCode(o.code);
   * });
   * // => { 'a': { 'dir': 'left', 'code': 97 }, 'd': { 'dir': 'right', 'code': 100 } }
   *
   * _.keyBy(array, 'dir');
   * // => { 'left': { 'dir': 'left', 'code': 97 }, 'right': { 'dir': 'right', 'code': 100 } }
   */
  var keyBy = createAggregator(function(result, value, key) {
    baseAssignValue(result, key, value)
  })

  /**
   * A specialized version of `_.lastIndexOf` which performs strict equality
   * comparisons of values, i.e. `===`.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function strictLastIndexOf(array, value, fromIndex) {
    var index = fromIndex + 1
    while (index--) {
      if (array[index] === value) {
        return index
      }
    }
    return index
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$b = Math.max,
    nativeMin$7 = Math.min

  /**
   * This method is like `_.indexOf` except that it iterates over elements of
   * `array` from right to left.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} [fromIndex=array.length-1] The index to search from.
   * @returns {number} Returns the index of the matched value, else `-1`.
   * @example
   *
   * _.lastIndexOf([1, 2, 1, 2], 2);
   * // => 3
   *
   * // Search from the `fromIndex`.
   * _.lastIndexOf([1, 2, 1, 2], 2, 2);
   * // => 1
   */
  function lastIndexOf(array, value, fromIndex) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return -1
    }
    var index = length
    if (fromIndex !== undefined) {
      index = toInteger(fromIndex)
      index =
        index < 0
          ? nativeMax$b(length + index, 0)
          : nativeMin$7(index, length - 1)
    }
    return value === value
      ? strictLastIndexOf(array, value, index)
      : baseFindIndex(array, baseIsNaN, index, true)
  }

  /**
   * Converts `string`, as space separated words, to lower case.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the lower cased string.
   * @example
   *
   * _.lowerCase('--Foo-Bar--');
   * // => 'foo bar'
   *
   * _.lowerCase('fooBar');
   * // => 'foo bar'
   *
   * _.lowerCase('__FOO_BAR__');
   * // => 'foo bar'
   */
  var lowerCase = createCompounder(function(result, word, index) {
    return result + (index ? ' ' : '') + word.toLowerCase()
  })

  /**
   * Converts the first character of `string` to lower case.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the converted string.
   * @example
   *
   * _.lowerFirst('Fred');
   * // => 'fred'
   *
   * _.lowerFirst('FRED');
   * // => 'fRED'
   */
  var lowerFirst = createCaseFirst('toLowerCase')

  /**
   * The base implementation of `_.lt` which doesn't coerce arguments.
   *
   * @private
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if `value` is less than `other`,
   *  else `false`.
   */
  function baseLt(value, other) {
    return value < other
  }

  /**
   * Checks if `value` is less than `other`.
   *
   * @static
   * @memberOf _
   * @since 3.9.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if `value` is less than `other`,
   *  else `false`.
   * @see _.gt
   * @example
   *
   * _.lt(1, 3);
   * // => true
   *
   * _.lt(3, 3);
   * // => false
   *
   * _.lt(3, 1);
   * // => false
   */
  var lt$1 = createRelationalOperation(baseLt)

  /**
   * Checks if `value` is less than or equal to `other`.
   *
   * @static
   * @memberOf _
   * @since 3.9.0
   * @category Lang
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {boolean} Returns `true` if `value` is less than or equal to
   *  `other`, else `false`.
   * @see _.gte
   * @example
   *
   * _.lte(1, 3);
   * // => true
   *
   * _.lte(3, 3);
   * // => true
   *
   * _.lte(3, 1);
   * // => false
   */
  var lte$1 = createRelationalOperation(function(value, other) {
    return value <= other
  })

  /**
   * The opposite of `_.mapValues`; this method creates an object with the
   * same values as `object` and keys generated by running each own enumerable
   * string keyed property of `object` thru `iteratee`. The iteratee is invoked
   * with three arguments: (value, key, object).
   *
   * @static
   * @memberOf _
   * @since 3.8.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns the new mapped object.
   * @see _.mapValues
   * @example
   *
   * _.mapKeys({ 'a': 1, 'b': 2 }, function(value, key) {
   *   return key + value;
   * });
   * // => { 'a1': 1, 'b2': 2 }
   */
  function mapKeys(object, iteratee) {
    var result = {}
    iteratee = baseIteratee(iteratee)

    baseForOwn(object, function(value, key, object) {
      baseAssignValue(result, iteratee(value, key, object), value)
    })
    return result
  }

  /**
   * Creates an object with the same keys as `object` and values generated
   * by running each own enumerable string keyed property of `object` thru
   * `iteratee`. The iteratee is invoked with three arguments:
   * (value, key, object).
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Object} Returns the new mapped object.
   * @see _.mapKeys
   * @example
   *
   * var users = {
   *   'fred':    { 'user': 'fred',    'age': 40 },
   *   'pebbles': { 'user': 'pebbles', 'age': 1 }
   * };
   *
   * _.mapValues(users, function(o) { return o.age; });
   * // => { 'fred': 40, 'pebbles': 1 } (iteration order is not guaranteed)
   *
   * // The `_.property` iteratee shorthand.
   * _.mapValues(users, 'age');
   * // => { 'fred': 40, 'pebbles': 1 } (iteration order is not guaranteed)
   */
  function mapValues(object, iteratee) {
    var result = {}
    iteratee = baseIteratee(iteratee)

    baseForOwn(object, function(value, key, object) {
      baseAssignValue(result, key, iteratee(value, key, object))
    })
    return result
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$5 = 1

  /**
   * Creates a function that performs a partial deep comparison between a given
   * object and `source`, returning `true` if the given object has equivalent
   * property values, else `false`.
   *
   * **Note:** The created function is equivalent to `_.isMatch` with `source`
   * partially applied.
   *
   * Partial comparisons will match empty array and empty object `source`
   * values against any array or object value, respectively. See `_.isEqual`
   * for a list of supported value comparisons.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Util
   * @param {Object} source The object of property values to match.
   * @returns {Function} Returns the new spec function.
   * @example
   *
   * var objects = [
   *   { 'a': 1, 'b': 2, 'c': 3 },
   *   { 'a': 4, 'b': 5, 'c': 6 }
   * ];
   *
   * _.filter(objects, _.matches({ 'a': 4, 'c': 6 }));
   * // => [{ 'a': 4, 'b': 5, 'c': 6 }]
   */
  function matches(source) {
    return baseMatches(baseClone(source, CLONE_DEEP_FLAG$5))
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$6 = 1

  /**
   * Creates a function that performs a partial deep comparison between the
   * value at `path` of a given object to `srcValue`, returning `true` if the
   * object value is equivalent, else `false`.
   *
   * **Note:** Partial comparisons will match empty array and empty object
   * `srcValue` values against any array or object value, respectively. See
   * `_.isEqual` for a list of supported value comparisons.
   *
   * @static
   * @memberOf _
   * @since 3.2.0
   * @category Util
   * @param {Array|string} path The path of the property to get.
   * @param {*} srcValue The value to match.
   * @returns {Function} Returns the new spec function.
   * @example
   *
   * var objects = [
   *   { 'a': 1, 'b': 2, 'c': 3 },
   *   { 'a': 4, 'b': 5, 'c': 6 }
   * ];
   *
   * _.find(objects, _.matchesProperty('a', 4));
   * // => { 'a': 4, 'b': 5, 'c': 6 }
   */
  function matchesProperty(path, srcValue) {
    return baseMatchesProperty(path, baseClone(srcValue, CLONE_DEEP_FLAG$6))
  }

  /**
   * The base implementation of methods like `_.max` and `_.min` which accepts a
   * `comparator` to determine the extremum value.
   *
   * @private
   * @param {Array} array The array to iterate over.
   * @param {Function} iteratee The iteratee invoked per iteration.
   * @param {Function} comparator The comparator used to compare values.
   * @returns {*} Returns the extremum value.
   */
  function baseExtremum(array, iteratee, comparator) {
    var index = -1,
      length = array.length

    while (++index < length) {
      var value = array[index],
        current = iteratee(value)

      if (
        current != null &&
        (computed === undefined
          ? current === current && !isSymbol(current)
          : comparator(current, computed))
      ) {
        var computed = current,
          result = value
      }
    }
    return result
  }

  /**
   * Computes the maximum value of `array`. If `array` is empty or falsey,
   * `undefined` is returned.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Math
   * @param {Array} array The array to iterate over.
   * @returns {*} Returns the maximum value.
   * @example
   *
   * _.max([4, 2, 8, 6]);
   * // => 8
   *
   * _.max([]);
   * // => undefined
   */
  function max$1(array) {
    return array && array.length
      ? baseExtremum(array, identity, baseGt)
      : undefined
  }

  /**
   * This method is like `_.max` except that it accepts `iteratee` which is
   * invoked for each element in `array` to generate the criterion by which
   * the value is ranked. The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Math
   * @param {Array} array The array to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {*} Returns the maximum value.
   * @example
   *
   * var objects = [{ 'n': 1 }, { 'n': 2 }];
   *
   * _.maxBy(objects, function(o) { return o.n; });
   * // => { 'n': 2 }
   *
   * // The `_.property` iteratee shorthand.
   * _.maxBy(objects, 'n');
   * // => { 'n': 2 }
   */
  function maxBy(array, iteratee) {
    return array && array.length
      ? baseExtremum(array, baseIteratee(iteratee), baseGt)
      : undefined
  }

  /**
   * The base implementation of `_.sum` and `_.sumBy` without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {number} Returns the sum.
   */
  function baseSum(array, iteratee) {
    var result,
      index = -1,
      length = array.length

    while (++index < length) {
      var current = iteratee(array[index])
      if (current !== undefined) {
        result = result === undefined ? current : result + current
      }
    }
    return result
  }

  /** Used as references for various `Number` constants. */
  var NAN$2 = 0 / 0

  /**
   * The base implementation of `_.mean` and `_.meanBy` without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @returns {number} Returns the mean.
   */
  function baseMean(array, iteratee) {
    var length = array == null ? 0 : array.length
    return length ? baseSum(array, iteratee) / length : NAN$2
  }

  /**
   * Computes the mean of the values in `array`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Math
   * @param {Array} array The array to iterate over.
   * @returns {number} Returns the mean.
   * @example
   *
   * _.mean([4, 2, 8, 6]);
   * // => 5
   */
  function mean(array) {
    return baseMean(array, identity)
  }

  /**
   * This method is like `_.mean` except that it accepts `iteratee` which is
   * invoked for each element in `array` to generate the value to be averaged.
   * The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.7.0
   * @category Math
   * @param {Array} array The array to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {number} Returns the mean.
   * @example
   *
   * var objects = [{ 'n': 4 }, { 'n': 2 }, { 'n': 8 }, { 'n': 6 }];
   *
   * _.meanBy(objects, function(o) { return o.n; });
   * // => 5
   *
   * // The `_.property` iteratee shorthand.
   * _.meanBy(objects, 'n');
   * // => 5
   */
  function meanBy(array, iteratee) {
    return baseMean(array, baseIteratee(iteratee))
  }

  /**
   * This method is like `_.assign` except that it recursively merges own and
   * inherited enumerable string keyed properties of source objects into the
   * destination object. Source properties that resolve to `undefined` are
   * skipped if a destination value exists. Array and plain object properties
   * are merged recursively. Other objects and value types are overridden by
   * assignment. Source objects are applied from left to right. Subsequent
   * sources overwrite property assignments of previous sources.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 0.5.0
   * @category Object
   * @param {Object} object The destination object.
   * @param {...Object} [sources] The source objects.
   * @returns {Object} Returns `object`.
   * @example
   *
   * var object = {
   *   'a': [{ 'b': 2 }, { 'd': 4 }]
   * };
   *
   * var other = {
   *   'a': [{ 'c': 3 }, { 'e': 5 }]
   * };
   *
   * _.merge(object, other);
   * // => { 'a': [{ 'b': 2, 'c': 3 }, { 'd': 4, 'e': 5 }] }
   */
  var merge$1 = createAssigner(function(object, source, srcIndex) {
    baseMerge(object, source, srcIndex)
  })

  /**
   * Creates a function that invokes the method at `path` of a given object.
   * Any additional arguments are provided to the invoked method.
   *
   * @static
   * @memberOf _
   * @since 3.7.0
   * @category Util
   * @param {Array|string} path The path of the method to invoke.
   * @param {...*} [args] The arguments to invoke the method with.
   * @returns {Function} Returns the new invoker function.
   * @example
   *
   * var objects = [
   *   { 'a': { 'b': _.constant(2) } },
   *   { 'a': { 'b': _.constant(1) } }
   * ];
   *
   * _.map(objects, _.method('a.b'));
   * // => [2, 1]
   *
   * _.map(objects, _.method(['a', 'b']));
   * // => [2, 1]
   */
  var method = baseRest(function(path, args) {
    return function(object) {
      return baseInvoke(object, path, args)
    }
  })

  /**
   * The opposite of `_.method`; this method creates a function that invokes
   * the method at a given path of `object`. Any additional arguments are
   * provided to the invoked method.
   *
   * @static
   * @memberOf _
   * @since 3.7.0
   * @category Util
   * @param {Object} object The object to query.
   * @param {...*} [args] The arguments to invoke the method with.
   * @returns {Function} Returns the new invoker function.
   * @example
   *
   * var array = _.times(3, _.constant),
   *     object = { 'a': array, 'b': array, 'c': array };
   *
   * _.map(['a[2]', 'c[0]'], _.methodOf(object));
   * // => [2, 0]
   *
   * _.map([['a', '2'], ['c', '0']], _.methodOf(object));
   * // => [2, 0]
   */
  var methodOf = baseRest(function(object, args) {
    return function(path) {
      return baseInvoke(object, path, args)
    }
  })

  /**
   * Computes the minimum value of `array`. If `array` is empty or falsey,
   * `undefined` is returned.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Math
   * @param {Array} array The array to iterate over.
   * @returns {*} Returns the minimum value.
   * @example
   *
   * _.min([4, 2, 8, 6]);
   * // => 2
   *
   * _.min([]);
   * // => undefined
   */
  function min$1(array) {
    return array && array.length
      ? baseExtremum(array, identity, baseLt)
      : undefined
  }

  /**
   * This method is like `_.min` except that it accepts `iteratee` which is
   * invoked for each element in `array` to generate the criterion by which
   * the value is ranked. The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Math
   * @param {Array} array The array to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {*} Returns the minimum value.
   * @example
   *
   * var objects = [{ 'n': 1 }, { 'n': 2 }];
   *
   * _.minBy(objects, function(o) { return o.n; });
   * // => { 'n': 1 }
   *
   * // The `_.property` iteratee shorthand.
   * _.minBy(objects, 'n');
   * // => { 'n': 1 }
   */
  function minBy(array, iteratee) {
    return array && array.length
      ? baseExtremum(array, baseIteratee(iteratee), baseLt)
      : undefined
  }

  /**
   * Adds all own enumerable string keyed function properties of a source
   * object to the destination object. If `object` is a function, then methods
   * are added to its prototype as well.
   *
   * **Note:** Use `_.runInContext` to create a pristine `lodash` function to
   * avoid conflicts caused by modifying the original.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {Function|Object} [object=lodash] The destination object.
   * @param {Object} source The object of functions to add.
   * @param {Object} [options={}] The options object.
   * @param {boolean} [options.chain=true] Specify whether mixins are chainable.
   * @returns {Function|Object} Returns `object`.
   * @example
   *
   * function vowels(string) {
   *   return _.filter(string, function(v) {
   *     return /[aeiou]/i.test(v);
   *   });
   * }
   *
   * _.mixin({ 'vowels': vowels });
   * _.vowels('fred');
   * // => ['e']
   *
   * _('fred').vowels().value();
   * // => ['e']
   *
   * _.mixin({ 'vowels': vowels }, { 'chain': false });
   * _('fred').vowels();
   * // => ['e']
   */
  function mixin(object, source, options) {
    var props = keys(source),
      methodNames = baseFunctions(source, props)

    var chain = !(isObject(options) && 'chain' in options) || !!options.chain,
      isFunc = isFunction(object)

    arrayEach(methodNames, function(methodName) {
      var func = source[methodName]
      object[methodName] = func
      if (isFunc) {
        object.prototype[methodName] = function() {
          var chainAll = this.__chain__
          if (chain || chainAll) {
            var result = object(this.__wrapped__),
              actions = (result.__actions__ = copyArray(this.__actions__))

            actions.push({ func: func, args: arguments, thisArg: object })
            result.__chain__ = chainAll
            return result
          }
          return func.apply(object, arrayPush([this.value()], arguments))
        }
      }
    })

    return object
  }

  /**
   * Multiply two numbers.
   *
   * @static
   * @memberOf _
   * @since 4.7.0
   * @category Math
   * @param {number} multiplier The first number in a multiplication.
   * @param {number} multiplicand The second number in a multiplication.
   * @returns {number} Returns the product.
   * @example
   *
   * _.multiply(6, 4);
   * // => 24
   */
  var multiply = createMathOperation(function(multiplier, multiplicand) {
    return multiplier * multiplicand
  }, 1)

  /** Error message constants. */
  var FUNC_ERROR_TEXT$8 = 'Expected a function'

  /**
   * Creates a function that negates the result of the predicate `func`. The
   * `func` predicate is invoked with the `this` binding and arguments of the
   * created function.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Function
   * @param {Function} predicate The predicate to negate.
   * @returns {Function} Returns the new negated function.
   * @example
   *
   * function isEven(n) {
   *   return n % 2 == 0;
   * }
   *
   * _.filter([1, 2, 3, 4, 5, 6], _.negate(isEven));
   * // => [1, 3, 5]
   */
  function negate(predicate) {
    if (typeof predicate != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$8)
    }
    return function() {
      var args = arguments
      switch (args.length) {
        case 0:
          return !predicate.call(this)
        case 1:
          return !predicate.call(this, args[0])
        case 2:
          return !predicate.call(this, args[0], args[1])
        case 3:
          return !predicate.call(this, args[0], args[1], args[2])
      }
      return !predicate.apply(this, args)
    }
  }

  /**
   * Converts `iterator` to an array.
   *
   * @private
   * @param {Object} iterator The iterator to convert.
   * @returns {Array} Returns the converted array.
   */
  function iteratorToArray(iterator) {
    var data,
      result = []

    while (!(data = iterator.next()).done) {
      result.push(data.value)
    }
    return result
  }

  /** `Object#toString` result references. */
  var mapTag$8 = '[object Map]',
    setTag$8 = '[object Set]'

  /** Built-in value references. */
  var symIterator = Symbol$1 ? Symbol$1.iterator : undefined

  /**
   * Converts `value` to an array.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {Array} Returns the converted array.
   * @example
   *
   * _.toArray({ 'a': 1, 'b': 2 });
   * // => [1, 2]
   *
   * _.toArray('abc');
   * // => ['a', 'b', 'c']
   *
   * _.toArray(1);
   * // => []
   *
   * _.toArray(null);
   * // => []
   */
  function toArray(value) {
    if (!value) {
      return []
    }
    if (isArrayLike(value)) {
      return isString(value) ? stringToArray(value) : copyArray(value)
    }
    if (symIterator && value[symIterator]) {
      return iteratorToArray(value[symIterator]())
    }
    var tag = getTag$1(value),
      func =
        tag == mapTag$8 ? mapToArray : tag == setTag$8 ? setToArray : values

    return func(value)
  }

  /**
   * Gets the next value on a wrapped object following the
   * [iterator protocol](https://mdn.io/iteration_protocols#iterator).
   *
   * @name next
   * @memberOf _
   * @since 4.0.0
   * @category Seq
   * @returns {Object} Returns the next iterator value.
   * @example
   *
   * var wrapped = _([1, 2]);
   *
   * wrapped.next();
   * // => { 'done': false, 'value': 1 }
   *
   * wrapped.next();
   * // => { 'done': false, 'value': 2 }
   *
   * wrapped.next();
   * // => { 'done': true, 'value': undefined }
   */
  function wrapperNext() {
    if (this.__values__ === undefined) {
      this.__values__ = toArray(this.value())
    }
    var done = this.__index__ >= this.__values__.length,
      value = done ? undefined : this.__values__[this.__index__++]

    return { done: done, value: value }
  }

  /**
   * The base implementation of `_.nth` which doesn't coerce arguments.
   *
   * @private
   * @param {Array} array The array to query.
   * @param {number} n The index of the element to return.
   * @returns {*} Returns the nth element of `array`.
   */
  function baseNth(array, n) {
    var length = array.length
    if (!length) {
      return
    }
    n += n < 0 ? length : 0
    return isIndex(n, length) ? array[n] : undefined
  }

  /**
   * Gets the element at index `n` of `array`. If `n` is negative, the nth
   * element from the end is returned.
   *
   * @static
   * @memberOf _
   * @since 4.11.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {number} [n=0] The index of the element to return.
   * @returns {*} Returns the nth element of `array`.
   * @example
   *
   * var array = ['a', 'b', 'c', 'd'];
   *
   * _.nth(array, 1);
   * // => 'b'
   *
   * _.nth(array, -2);
   * // => 'c';
   */
  function nth(array, n) {
    return array && array.length ? baseNth(array, toInteger(n)) : undefined
  }

  /**
   * Creates a function that gets the argument at index `n`. If `n` is negative,
   * the nth argument from the end is returned.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {number} [n=0] The index of the argument to return.
   * @returns {Function} Returns the new pass-thru function.
   * @example
   *
   * var func = _.nthArg(1);
   * func('a', 'b', 'c', 'd');
   * // => 'b'
   *
   * var func = _.nthArg(-2);
   * func('a', 'b', 'c', 'd');
   * // => 'c'
   */
  function nthArg(n) {
    n = toInteger(n)
    return baseRest(function(args) {
      return baseNth(args, n)
    })
  }

  /**
   * The base implementation of `_.unset`.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {Array|string} path The property path to unset.
   * @returns {boolean} Returns `true` if the property is deleted, else `false`.
   */
  function baseUnset(object, path) {
    path = castPath(path, object)
    object = parent(object, path)
    return object == null || delete object[toKey(last(path))]
  }

  /**
   * Used by `_.omit` to customize its `_.cloneDeep` use to only clone plain
   * objects.
   *
   * @private
   * @param {*} value The value to inspect.
   * @param {string} key The key of the property to inspect.
   * @returns {*} Returns the uncloned value or `undefined` to defer cloning to `_.cloneDeep`.
   */
  function customOmitClone(value) {
    return isPlainObject(value) ? undefined : value
  }

  /** Used to compose bitmasks for cloning. */
  var CLONE_DEEP_FLAG$7 = 1,
    CLONE_FLAT_FLAG$1 = 2,
    CLONE_SYMBOLS_FLAG$5 = 4

  /**
   * The opposite of `_.pick`; this method creates an object composed of the
   * own and inherited enumerable property paths of `object` that are not omitted.
   *
   * **Note:** This method is considerably slower than `_.pick`.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The source object.
   * @param {...(string|string[])} [paths] The property paths to omit.
   * @returns {Object} Returns the new object.
   * @example
   *
   * var object = { 'a': 1, 'b': '2', 'c': 3 };
   *
   * _.omit(object, ['a', 'c']);
   * // => { 'b': '2' }
   */
  var omit = flatRest(function(object, paths) {
    var result = {}
    if (object == null) {
      return result
    }
    var isDeep = false
    paths = arrayMap(paths, function(path) {
      path = castPath(path, object)
      isDeep || (isDeep = path.length > 1)
      return path
    })
    copyObject(object, getAllKeysIn(object), result)
    if (isDeep) {
      result = baseClone(
        result,
        CLONE_DEEP_FLAG$7 | CLONE_FLAT_FLAG$1 | CLONE_SYMBOLS_FLAG$5,
        customOmitClone
      )
    }
    var length = paths.length
    while (length--) {
      baseUnset(result, paths[length])
    }
    return result
  })

  /**
   * The base implementation of `_.set`.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to set.
   * @param {*} value The value to set.
   * @param {Function} [customizer] The function to customize path creation.
   * @returns {Object} Returns `object`.
   */
  function baseSet(object, path, value, customizer) {
    if (!isObject(object)) {
      return object
    }
    path = castPath(path, object)

    var index = -1,
      length = path.length,
      lastIndex = length - 1,
      nested = object

    while (nested != null && ++index < length) {
      var key = toKey(path[index]),
        newValue = value

      if (index != lastIndex) {
        var objValue = nested[key]
        newValue = customizer ? customizer(objValue, key, nested) : undefined
        if (newValue === undefined) {
          newValue = isObject(objValue)
            ? objValue
            : isIndex(path[index + 1])
            ? []
            : {}
        }
      }
      assignValue(nested, key, newValue)
      nested = nested[key]
    }
    return object
  }

  /**
   * The base implementation of  `_.pickBy` without support for iteratee shorthands.
   *
   * @private
   * @param {Object} object The source object.
   * @param {string[]} paths The property paths to pick.
   * @param {Function} predicate The function invoked per property.
   * @returns {Object} Returns the new object.
   */
  function basePickBy(object, paths, predicate) {
    var index = -1,
      length = paths.length,
      result = {}

    while (++index < length) {
      var path = paths[index],
        value = baseGet(object, path)

      if (predicate(value, path)) {
        baseSet(result, castPath(path, object), value)
      }
    }
    return result
  }

  /**
   * Creates an object composed of the `object` properties `predicate` returns
   * truthy for. The predicate is invoked with two arguments: (value, key).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The source object.
   * @param {Function} [predicate=_.identity] The function invoked per property.
   * @returns {Object} Returns the new object.
   * @example
   *
   * var object = { 'a': 1, 'b': '2', 'c': 3 };
   *
   * _.pickBy(object, _.isNumber);
   * // => { 'a': 1, 'c': 3 }
   */
  function pickBy(object, predicate) {
    if (object == null) {
      return {}
    }
    var props = arrayMap(getAllKeysIn(object), function(prop) {
      return [prop]
    })
    predicate = baseIteratee(predicate)
    return basePickBy(object, props, function(value, path) {
      return predicate(value, path[0])
    })
  }

  /**
   * The opposite of `_.pickBy`; this method creates an object composed of
   * the own and inherited enumerable string keyed properties of `object` that
   * `predicate` doesn't return truthy for. The predicate is invoked with two
   * arguments: (value, key).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The source object.
   * @param {Function} [predicate=_.identity] The function invoked per property.
   * @returns {Object} Returns the new object.
   * @example
   *
   * var object = { 'a': 1, 'b': '2', 'c': 3 };
   *
   * _.omitBy(object, _.isNumber);
   * // => { 'b': '2' }
   */
  function omitBy(object, predicate) {
    return pickBy(object, negate(baseIteratee(predicate)))
  }

  /**
   * Creates a function that is restricted to invoking `func` once. Repeat calls
   * to the function return the value of the first invocation. The `func` is
   * invoked with the `this` binding and arguments of the created function.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to restrict.
   * @returns {Function} Returns the new restricted function.
   * @example
   *
   * var initialize = _.once(createApplication);
   * initialize();
   * initialize();
   * // => `createApplication` is invoked once
   */
  function once(func) {
    return before(2, func)
  }

  /**
   * The base implementation of `_.sortBy` which uses `comparer` to define the
   * sort order of `array` and replaces criteria objects with their corresponding
   * values.
   *
   * @private
   * @param {Array} array The array to sort.
   * @param {Function} comparer The function to define sort order.
   * @returns {Array} Returns `array`.
   */
  function baseSortBy(array, comparer) {
    var length = array.length

    array.sort(comparer)
    while (length--) {
      array[length] = array[length].value
    }
    return array
  }

  /**
   * Compares values to sort them in ascending order.
   *
   * @private
   * @param {*} value The value to compare.
   * @param {*} other The other value to compare.
   * @returns {number} Returns the sort order indicator for `value`.
   */
  function compareAscending(value, other) {
    if (value !== other) {
      var valIsDefined = value !== undefined,
        valIsNull = value === null,
        valIsReflexive = value === value,
        valIsSymbol = isSymbol(value)

      var othIsDefined = other !== undefined,
        othIsNull = other === null,
        othIsReflexive = other === other,
        othIsSymbol = isSymbol(other)

      if (
        (!othIsNull && !othIsSymbol && !valIsSymbol && value > other) ||
        (valIsSymbol &&
          othIsDefined &&
          othIsReflexive &&
          !othIsNull &&
          !othIsSymbol) ||
        (valIsNull && othIsDefined && othIsReflexive) ||
        (!valIsDefined && othIsReflexive) ||
        !valIsReflexive
      ) {
        return 1
      }
      if (
        (!valIsNull && !valIsSymbol && !othIsSymbol && value < other) ||
        (othIsSymbol &&
          valIsDefined &&
          valIsReflexive &&
          !valIsNull &&
          !valIsSymbol) ||
        (othIsNull && valIsDefined && valIsReflexive) ||
        (!othIsDefined && valIsReflexive) ||
        !othIsReflexive
      ) {
        return -1
      }
    }
    return 0
  }

  /**
   * Used by `_.orderBy` to compare multiple properties of a value to another
   * and stable sort them.
   *
   * If `orders` is unspecified, all values are sorted in ascending order. Otherwise,
   * specify an order of "desc" for descending or "asc" for ascending sort order
   * of corresponding values.
   *
   * @private
   * @param {Object} object The object to compare.
   * @param {Object} other The other object to compare.
   * @param {boolean[]|string[]} orders The order to sort by for each property.
   * @returns {number} Returns the sort order indicator for `object`.
   */
  function compareMultiple(object, other, orders) {
    var index = -1,
      objCriteria = object.criteria,
      othCriteria = other.criteria,
      length = objCriteria.length,
      ordersLength = orders.length

    while (++index < length) {
      var result = compareAscending(objCriteria[index], othCriteria[index])
      if (result) {
        if (index >= ordersLength) {
          return result
        }
        var order = orders[index]
        return result * (order == 'desc' ? -1 : 1)
      }
    }
    // Fixes an `Array#sort` bug in the JS engine embedded in Adobe applications
    // that causes it, under certain circumstances, to provide the same value for
    // `object` and `other`. See https://github.com/jashkenas/underscore/pull/1247
    // for more details.
    //
    // This also ensures a stable sort in V8 and other engines.
    // See https://bugs.chromium.org/p/v8/issues/detail?id=90 for more details.
    return object.index - other.index
  }

  /**
   * The base implementation of `_.orderBy` without param guards.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function[]|Object[]|string[]} iteratees The iteratees to sort by.
   * @param {string[]} orders The sort orders of `iteratees`.
   * @returns {Array} Returns the new sorted array.
   */
  function baseOrderBy(collection, iteratees, orders) {
    var index = -1
    iteratees = arrayMap(
      iteratees.length ? iteratees : [identity],
      baseUnary(baseIteratee)
    )

    var result = baseMap(collection, function(value, key, collection) {
      var criteria = arrayMap(iteratees, function(iteratee) {
        return iteratee(value)
      })
      return { criteria: criteria, index: ++index, value: value }
    })

    return baseSortBy(result, function(object, other) {
      return compareMultiple(object, other, orders)
    })
  }

  /**
   * This method is like `_.sortBy` except that it allows specifying the sort
   * orders of the iteratees to sort by. If `orders` is unspecified, all values
   * are sorted in ascending order. Otherwise, specify an order of "desc" for
   * descending or "asc" for ascending sort order of corresponding values.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Array[]|Function[]|Object[]|string[]} [iteratees=[_.identity]]
   *  The iteratees to sort by.
   * @param {string[]} [orders] The sort orders of `iteratees`.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.reduce`.
   * @returns {Array} Returns the new sorted array.
   * @example
   *
   * var users = [
   *   { 'user': 'fred',   'age': 48 },
   *   { 'user': 'barney', 'age': 34 },
   *   { 'user': 'fred',   'age': 40 },
   *   { 'user': 'barney', 'age': 36 }
   * ];
   *
   * // Sort by `user` in ascending order and by `age` in descending order.
   * _.orderBy(users, ['user', 'age'], ['asc', 'desc']);
   * // => objects for [['barney', 36], ['barney', 34], ['fred', 48], ['fred', 40]]
   */
  function orderBy(collection, iteratees, orders, guard) {
    if (collection == null) {
      return []
    }
    if (!isArray(iteratees)) {
      iteratees = iteratees == null ? [] : [iteratees]
    }
    orders = guard ? undefined : orders
    if (!isArray(orders)) {
      orders = orders == null ? [] : [orders]
    }
    return baseOrderBy(collection, iteratees, orders)
  }

  /**
   * Creates a function like `_.over`.
   *
   * @private
   * @param {Function} arrayFunc The function to iterate over iteratees.
   * @returns {Function} Returns the new over function.
   */
  function createOver(arrayFunc) {
    return flatRest(function(iteratees) {
      iteratees = arrayMap(iteratees, baseUnary(baseIteratee))
      return baseRest(function(args) {
        var thisArg = this
        return arrayFunc(iteratees, function(iteratee) {
          return apply(iteratee, thisArg, args)
        })
      })
    })
  }

  /**
   * Creates a function that invokes `iteratees` with the arguments it receives
   * and returns their results.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {...(Function|Function[])} [iteratees=[_.identity]]
   *  The iteratees to invoke.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var func = _.over([Math.max, Math.min]);
   *
   * func(1, 2, 3, 4);
   * // => [4, 1]
   */
  var over = createOver(arrayMap)

  /**
   * A `baseRest` alias which can be replaced with `identity` by module
   * replacement plugins.
   *
   * @private
   * @type {Function}
   * @param {Function} func The function to apply a rest parameter to.
   * @returns {Function} Returns the new function.
   */
  var castRest = baseRest

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin$8 = Math.min

  /**
   * Creates a function that invokes `func` with its arguments transformed.
   *
   * @static
   * @since 4.0.0
   * @memberOf _
   * @category Function
   * @param {Function} func The function to wrap.
   * @param {...(Function|Function[])} [transforms=[_.identity]]
   *  The argument transforms.
   * @returns {Function} Returns the new function.
   * @example
   *
   * function doubled(n) {
   *   return n * 2;
   * }
   *
   * function square(n) {
   *   return n * n;
   * }
   *
   * var func = _.overArgs(function(x, y) {
   *   return [x, y];
   * }, [square, doubled]);
   *
   * func(9, 3);
   * // => [81, 6]
   *
   * func(10, 5);
   * // => [100, 10]
   */
  var overArgs = castRest(function(func, transforms) {
    transforms =
      transforms.length == 1 && isArray(transforms[0])
        ? arrayMap(transforms[0], baseUnary(baseIteratee))
        : arrayMap(baseFlatten(transforms, 1), baseUnary(baseIteratee))

    var funcsLength = transforms.length
    return baseRest(function(args) {
      var index = -1,
        length = nativeMin$8(args.length, funcsLength)

      while (++index < length) {
        args[index] = transforms[index].call(this, args[index])
      }
      return apply(func, this, args)
    })
  })

  /**
   * Creates a function that checks if **all** of the `predicates` return
   * truthy when invoked with the arguments it receives.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {...(Function|Function[])} [predicates=[_.identity]]
   *  The predicates to check.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var func = _.overEvery([Boolean, isFinite]);
   *
   * func('1');
   * // => true
   *
   * func(null);
   * // => false
   *
   * func(NaN);
   * // => false
   */
  var overEvery = createOver(arrayEvery)

  /**
   * Creates a function that checks if **any** of the `predicates` return
   * truthy when invoked with the arguments it receives.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {...(Function|Function[])} [predicates=[_.identity]]
   *  The predicates to check.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var func = _.overSome([Boolean, isFinite]);
   *
   * func('1');
   * // => true
   *
   * func(null);
   * // => true
   *
   * func(NaN);
   * // => false
   */
  var overSome = createOver(arraySome)

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER$3 = 9007199254740991

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeFloor = Math.floor

  /**
   * The base implementation of `_.repeat` which doesn't coerce arguments.
   *
   * @private
   * @param {string} string The string to repeat.
   * @param {number} n The number of times to repeat the string.
   * @returns {string} Returns the repeated string.
   */
  function baseRepeat(string, n) {
    var result = ''
    if (!string || n < 1 || n > MAX_SAFE_INTEGER$3) {
      return result
    }
    // Leverage the exponentiation by squaring algorithm for a faster repeat.
    // See https://en.wikipedia.org/wiki/Exponentiation_by_squaring for more details.
    do {
      if (n % 2) {
        result += string
      }
      n = nativeFloor(n / 2)
      if (n) {
        string += string
      }
    } while (n)

    return result
  }

  /**
   * Gets the size of an ASCII `string`.
   *
   * @private
   * @param {string} string The string inspect.
   * @returns {number} Returns the string size.
   */
  var asciiSize = baseProperty('length')

  /** Used to compose unicode character classes. */
  var rsAstralRange$3 = '\\ud800-\\udfff',
    rsComboMarksRange$4 = '\\u0300-\\u036f',
    reComboHalfMarksRange$4 = '\\ufe20-\\ufe2f',
    rsComboSymbolsRange$4 = '\\u20d0-\\u20ff',
    rsComboRange$4 =
      rsComboMarksRange$4 + reComboHalfMarksRange$4 + rsComboSymbolsRange$4,
    rsVarRange$3 = '\\ufe0e\\ufe0f'

  /** Used to compose unicode capture groups. */
  var rsAstral$1 = '[' + rsAstralRange$3 + ']',
    rsCombo$3 = '[' + rsComboRange$4 + ']',
    rsFitz$2 = '\\ud83c[\\udffb-\\udfff]',
    rsModifier$2 = '(?:' + rsCombo$3 + '|' + rsFitz$2 + ')',
    rsNonAstral$2 = '[^' + rsAstralRange$3 + ']',
    rsRegional$2 = '(?:\\ud83c[\\udde6-\\uddff]){2}',
    rsSurrPair$2 = '[\\ud800-\\udbff][\\udc00-\\udfff]',
    rsZWJ$3 = '\\u200d'

  /** Used to compose unicode regexes. */
  var reOptMod$2 = rsModifier$2 + '?',
    rsOptVar$2 = '[' + rsVarRange$3 + ']?',
    rsOptJoin$2 =
      '(?:' +
      rsZWJ$3 +
      '(?:' +
      [rsNonAstral$2, rsRegional$2, rsSurrPair$2].join('|') +
      ')' +
      rsOptVar$2 +
      reOptMod$2 +
      ')*',
    rsSeq$2 = rsOptVar$2 + reOptMod$2 + rsOptJoin$2,
    rsSymbol$1 =
      '(?:' +
      [
        rsNonAstral$2 + rsCombo$3 + '?',
        rsCombo$3,
        rsRegional$2,
        rsSurrPair$2,
        rsAstral$1,
      ].join('|') +
      ')'

  /** Used to match [string symbols](https://mathiasbynens.be/notes/javascript-unicode). */
  var reUnicode$1 = RegExp(
    rsFitz$2 + '(?=' + rsFitz$2 + ')|' + rsSymbol$1 + rsSeq$2,
    'g'
  )

  /**
   * Gets the size of a Unicode `string`.
   *
   * @private
   * @param {string} string The string inspect.
   * @returns {number} Returns the string size.
   */
  function unicodeSize(string) {
    var result = (reUnicode$1.lastIndex = 0)
    while (reUnicode$1.test(string)) {
      ++result
    }
    return result
  }

  /**
   * Gets the number of symbols in `string`.
   *
   * @private
   * @param {string} string The string to inspect.
   * @returns {number} Returns the string size.
   */
  function stringSize(string) {
    return hasUnicode(string) ? unicodeSize(string) : asciiSize(string)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeCeil$1 = Math.ceil

  /**
   * Creates the padding for `string` based on `length`. The `chars` string
   * is truncated if the number of characters exceeds `length`.
   *
   * @private
   * @param {number} length The padding length.
   * @param {string} [chars=' '] The string used as padding.
   * @returns {string} Returns the padding for `string`.
   */
  function createPadding(length, chars) {
    chars = chars === undefined ? ' ' : baseToString(chars)

    var charsLength = chars.length
    if (charsLength < 2) {
      return charsLength ? baseRepeat(chars, length) : chars
    }
    var result = baseRepeat(chars, nativeCeil$1(length / stringSize(chars)))
    return hasUnicode(chars)
      ? castSlice(stringToArray(result), 0, length).join('')
      : result.slice(0, length)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeCeil$2 = Math.ceil,
    nativeFloor$1 = Math.floor

  /**
   * Pads `string` on the left and right sides if it's shorter than `length`.
   * Padding characters are truncated if they can't be evenly divided by `length`.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to pad.
   * @param {number} [length=0] The padding length.
   * @param {string} [chars=' '] The string used as padding.
   * @returns {string} Returns the padded string.
   * @example
   *
   * _.pad('abc', 8);
   * // => '  abc   '
   *
   * _.pad('abc', 8, '_-');
   * // => '_-abc_-_'
   *
   * _.pad('abc', 3);
   * // => 'abc'
   */
  function pad(string, length, chars) {
    string = toString(string)
    length = toInteger(length)

    var strLength = length ? stringSize(string) : 0
    if (!length || strLength >= length) {
      return string
    }
    var mid = (length - strLength) / 2
    return (
      createPadding(nativeFloor$1(mid), chars) +
      string +
      createPadding(nativeCeil$2(mid), chars)
    )
  }

  /**
   * Pads `string` on the right side if it's shorter than `length`. Padding
   * characters are truncated if they exceed `length`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to pad.
   * @param {number} [length=0] The padding length.
   * @param {string} [chars=' '] The string used as padding.
   * @returns {string} Returns the padded string.
   * @example
   *
   * _.padEnd('abc', 6);
   * // => 'abc   '
   *
   * _.padEnd('abc', 6, '_-');
   * // => 'abc_-_'
   *
   * _.padEnd('abc', 3);
   * // => 'abc'
   */
  function padEnd(string, length, chars) {
    string = toString(string)
    length = toInteger(length)

    var strLength = length ? stringSize(string) : 0
    return length && strLength < length
      ? string + createPadding(length - strLength, chars)
      : string
  }

  /**
   * Pads `string` on the left side if it's shorter than `length`. Padding
   * characters are truncated if they exceed `length`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to pad.
   * @param {number} [length=0] The padding length.
   * @param {string} [chars=' '] The string used as padding.
   * @returns {string} Returns the padded string.
   * @example
   *
   * _.padStart('abc', 6);
   * // => '   abc'
   *
   * _.padStart('abc', 6, '_-');
   * // => '_-_abc'
   *
   * _.padStart('abc', 3);
   * // => 'abc'
   */
  function padStart(string, length, chars) {
    string = toString(string)
    length = toInteger(length)

    var strLength = length ? stringSize(string) : 0
    return length && strLength < length
      ? createPadding(length - strLength, chars) + string
      : string
  }

  /** Used to match leading and trailing whitespace. */
  var reTrimStart = /^\s+/

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeParseInt = root.parseInt

  /**
   * Converts `string` to an integer of the specified radix. If `radix` is
   * `undefined` or `0`, a `radix` of `10` is used unless `value` is a
   * hexadecimal, in which case a `radix` of `16` is used.
   *
   * **Note:** This method aligns with the
   * [ES5 implementation](https://es5.github.io/#x15.1.2.2) of `parseInt`.
   *
   * @static
   * @memberOf _
   * @since 1.1.0
   * @category String
   * @param {string} string The string to convert.
   * @param {number} [radix=10] The radix to interpret `value` by.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {number} Returns the converted integer.
   * @example
   *
   * _.parseInt('08');
   * // => 8
   *
   * _.map(['6', '08', '10'], _.parseInt);
   * // => [6, 8, 10]
   */
  function parseInt$1(string, radix, guard) {
    if (guard || radix == null) {
      radix = 0
    } else if (radix) {
      radix = +radix
    }
    return nativeParseInt(toString(string).replace(reTrimStart, ''), radix || 0)
  }

  /** Used to compose bitmasks for function metadata. */
  var WRAP_PARTIAL_FLAG$6 = 32

  /**
   * Creates a function that invokes `func` with `partials` prepended to the
   * arguments it receives. This method is like `_.bind` except it does **not**
   * alter the `this` binding.
   *
   * The `_.partial.placeholder` value, which defaults to `_` in monolithic
   * builds, may be used as a placeholder for partially applied arguments.
   *
   * **Note:** This method doesn't set the "length" property of partially
   * applied functions.
   *
   * @static
   * @memberOf _
   * @since 0.2.0
   * @category Function
   * @param {Function} func The function to partially apply arguments to.
   * @param {...*} [partials] The arguments to be partially applied.
   * @returns {Function} Returns the new partially applied function.
   * @example
   *
   * function greet(greeting, name) {
   *   return greeting + ' ' + name;
   * }
   *
   * var sayHelloTo = _.partial(greet, 'hello');
   * sayHelloTo('fred');
   * // => 'hello fred'
   *
   * // Partially applied with placeholders.
   * var greetFred = _.partial(greet, _, 'fred');
   * greetFred('hi');
   * // => 'hi fred'
   */
  var partial = baseRest(function(func, partials) {
    var holders = replaceHolders(partials, getHolder(partial))
    return createWrap(func, WRAP_PARTIAL_FLAG$6, undefined, partials, holders)
  })

  // Assign default placeholders.
  partial.placeholder = {}

  /** Used to compose bitmasks for function metadata. */
  var WRAP_PARTIAL_RIGHT_FLAG$3 = 64

  /**
   * This method is like `_.partial` except that partially applied arguments
   * are appended to the arguments it receives.
   *
   * The `_.partialRight.placeholder` value, which defaults to `_` in monolithic
   * builds, may be used as a placeholder for partially applied arguments.
   *
   * **Note:** This method doesn't set the "length" property of partially
   * applied functions.
   *
   * @static
   * @memberOf _
   * @since 1.0.0
   * @category Function
   * @param {Function} func The function to partially apply arguments to.
   * @param {...*} [partials] The arguments to be partially applied.
   * @returns {Function} Returns the new partially applied function.
   * @example
   *
   * function greet(greeting, name) {
   *   return greeting + ' ' + name;
   * }
   *
   * var greetFred = _.partialRight(greet, 'fred');
   * greetFred('hi');
   * // => 'hi fred'
   *
   * // Partially applied with placeholders.
   * var sayHelloTo = _.partialRight(greet, 'hello', _);
   * sayHelloTo('fred');
   * // => 'hello fred'
   */
  var partialRight = baseRest(function(func, partials) {
    var holders = replaceHolders(partials, getHolder(partialRight))
    return createWrap(
      func,
      WRAP_PARTIAL_RIGHT_FLAG$3,
      undefined,
      partials,
      holders
    )
  })

  // Assign default placeholders.
  partialRight.placeholder = {}

  /**
   * Creates an array of elements split into two groups, the first of which
   * contains elements `predicate` returns truthy for, the second of which
   * contains elements `predicate` returns falsey for. The predicate is
   * invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the array of grouped elements.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'age': 36, 'active': false },
   *   { 'user': 'fred',    'age': 40, 'active': true },
   *   { 'user': 'pebbles', 'age': 1,  'active': false }
   * ];
   *
   * _.partition(users, function(o) { return o.active; });
   * // => objects for [['fred'], ['barney', 'pebbles']]
   *
   * // The `_.matches` iteratee shorthand.
   * _.partition(users, { 'age': 1, 'active': false });
   * // => objects for [['pebbles'], ['barney', 'fred']]
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.partition(users, ['active', false]);
   * // => objects for [['barney', 'pebbles'], ['fred']]
   *
   * // The `_.property` iteratee shorthand.
   * _.partition(users, 'active');
   * // => objects for [['fred'], ['barney', 'pebbles']]
   */
  var partition = createAggregator(
    function(result, value, key) {
      result[key ? 0 : 1].push(value)
    },
    function() {
      return [[], []]
    }
  )

  /**
   * The base implementation of `_.pick` without support for individual
   * property identifiers.
   *
   * @private
   * @param {Object} object The source object.
   * @param {string[]} paths The property paths to pick.
   * @returns {Object} Returns the new object.
   */
  function basePick(object, paths) {
    return basePickBy(object, paths, function(value, path) {
      return hasIn(object, path)
    })
  }

  /**
   * Creates an object composed of the picked `object` properties.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The source object.
   * @param {...(string|string[])} [paths] The property paths to pick.
   * @returns {Object} Returns the new object.
   * @example
   *
   * var object = { 'a': 1, 'b': '2', 'c': 3 };
   *
   * _.pick(object, ['a', 'c']);
   * // => { 'a': 1, 'c': 3 }
   */
  var pick = flatRest(function(object, paths) {
    return object == null ? {} : basePick(object, paths)
  })

  /**
   * Creates a clone of the chain sequence planting `value` as the wrapped value.
   *
   * @name plant
   * @memberOf _
   * @since 3.2.0
   * @category Seq
   * @param {*} value The value to plant.
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * function square(n) {
   *   return n * n;
   * }
   *
   * var wrapped = _([1, 2]).map(square);
   * var other = wrapped.plant([3, 4]);
   *
   * other.value();
   * // => [9, 16]
   *
   * wrapped.value();
   * // => [1, 4]
   */
  function wrapperPlant(value) {
    var result,
      parent = this

    while (parent instanceof baseLodash) {
      var clone = wrapperClone(parent)
      clone.__index__ = 0
      clone.__values__ = undefined
      if (result) {
        previous.__wrapped__ = clone
      } else {
        result = clone
      }
      var previous = clone
      parent = parent.__wrapped__
    }
    previous.__wrapped__ = value
    return result
  }

  /**
   * The opposite of `_.property`; this method creates a function that returns
   * the value at a given path of `object`.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Util
   * @param {Object} object The object to query.
   * @returns {Function} Returns the new accessor function.
   * @example
   *
   * var array = [0, 1, 2],
   *     object = { 'a': array, 'b': array, 'c': array };
   *
   * _.map(['a[2]', 'c[0]'], _.propertyOf(object));
   * // => [2, 0]
   *
   * _.map([['a', '2'], ['c', '0']], _.propertyOf(object));
   * // => [2, 0]
   */
  function propertyOf(object) {
    return function(path) {
      return object == null ? undefined : baseGet(object, path)
    }
  }

  /**
   * This function is like `baseIndexOf` except that it accepts a comparator.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @param {number} fromIndex The index to search from.
   * @param {Function} comparator The comparator invoked per element.
   * @returns {number} Returns the index of the matched value, else `-1`.
   */
  function baseIndexOfWith(array, value, fromIndex, comparator) {
    var index = fromIndex - 1,
      length = array.length

    while (++index < length) {
      if (comparator(array[index], value)) {
        return index
      }
    }
    return -1
  }

  /** Used for built-in method references. */
  var arrayProto$2 = Array.prototype

  /** Built-in value references. */
  var splice$1 = arrayProto$2.splice

  /**
   * The base implementation of `_.pullAllBy` without support for iteratee
   * shorthands.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {Array} values The values to remove.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns `array`.
   */
  function basePullAll(array, values, iteratee, comparator) {
    var indexOf = comparator ? baseIndexOfWith : baseIndexOf,
      index = -1,
      length = values.length,
      seen = array

    if (array === values) {
      values = copyArray(values)
    }
    if (iteratee) {
      seen = arrayMap(array, baseUnary(iteratee))
    }
    while (++index < length) {
      var fromIndex = 0,
        value = values[index],
        computed = iteratee ? iteratee(value) : value

      while (
        (fromIndex = indexOf(seen, computed, fromIndex, comparator)) > -1
      ) {
        if (seen !== array) {
          splice$1.call(seen, fromIndex, 1)
        }
        splice$1.call(array, fromIndex, 1)
      }
    }
    return array
  }

  /**
   * This method is like `_.pull` except that it accepts an array of values to remove.
   *
   * **Note:** Unlike `_.difference`, this method mutates `array`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to modify.
   * @param {Array} values The values to remove.
   * @returns {Array} Returns `array`.
   * @example
   *
   * var array = ['a', 'b', 'c', 'a', 'b', 'c'];
   *
   * _.pullAll(array, ['a', 'c']);
   * console.log(array);
   * // => ['b', 'b']
   */
  function pullAll(array, values) {
    return array && array.length && values && values.length
      ? basePullAll(array, values)
      : array
  }

  /**
   * Removes all given values from `array` using
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons.
   *
   * **Note:** Unlike `_.without`, this method mutates `array`. Use `_.remove`
   * to remove elements from an array by predicate.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Array
   * @param {Array} array The array to modify.
   * @param {...*} [values] The values to remove.
   * @returns {Array} Returns `array`.
   * @example
   *
   * var array = ['a', 'b', 'c', 'a', 'b', 'c'];
   *
   * _.pull(array, 'a', 'c');
   * console.log(array);
   * // => ['b', 'b']
   */
  var pull = baseRest(pullAll)

  /**
   * This method is like `_.pullAll` except that it accepts `iteratee` which is
   * invoked for each element of `array` and `values` to generate the criterion
   * by which they're compared. The iteratee is invoked with one argument: (value).
   *
   * **Note:** Unlike `_.differenceBy`, this method mutates `array`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to modify.
   * @param {Array} values The values to remove.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Array} Returns `array`.
   * @example
   *
   * var array = [{ 'x': 1 }, { 'x': 2 }, { 'x': 3 }, { 'x': 1 }];
   *
   * _.pullAllBy(array, [{ 'x': 1 }, { 'x': 3 }], 'x');
   * console.log(array);
   * // => [{ 'x': 2 }]
   */
  function pullAllBy(array, values, iteratee) {
    return array && array.length && values && values.length
      ? basePullAll(array, values, baseIteratee(iteratee))
      : array
  }

  /**
   * This method is like `_.pullAll` except that it accepts `comparator` which
   * is invoked to compare elements of `array` to `values`. The comparator is
   * invoked with two arguments: (arrVal, othVal).
   *
   * **Note:** Unlike `_.differenceWith`, this method mutates `array`.
   *
   * @static
   * @memberOf _
   * @since 4.6.0
   * @category Array
   * @param {Array} array The array to modify.
   * @param {Array} values The values to remove.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns `array`.
   * @example
   *
   * var array = [{ 'x': 1, 'y': 2 }, { 'x': 3, 'y': 4 }, { 'x': 5, 'y': 6 }];
   *
   * _.pullAllWith(array, [{ 'x': 3, 'y': 4 }], _.isEqual);
   * console.log(array);
   * // => [{ 'x': 1, 'y': 2 }, { 'x': 5, 'y': 6 }]
   */
  function pullAllWith(array, values, comparator) {
    return array && array.length && values && values.length
      ? basePullAll(array, values, undefined, comparator)
      : array
  }

  /** Used for built-in method references. */
  var arrayProto$3 = Array.prototype

  /** Built-in value references. */
  var splice$2 = arrayProto$3.splice

  /**
   * The base implementation of `_.pullAt` without support for individual
   * indexes or capturing the removed elements.
   *
   * @private
   * @param {Array} array The array to modify.
   * @param {number[]} indexes The indexes of elements to remove.
   * @returns {Array} Returns `array`.
   */
  function basePullAt(array, indexes) {
    var length = array ? indexes.length : 0,
      lastIndex = length - 1

    while (length--) {
      var index = indexes[length]
      if (length == lastIndex || index !== previous) {
        var previous = index
        if (isIndex(index)) {
          splice$2.call(array, index, 1)
        } else {
          baseUnset(array, index)
        }
      }
    }
    return array
  }

  /**
   * Removes elements from `array` corresponding to `indexes` and returns an
   * array of removed elements.
   *
   * **Note:** Unlike `_.at`, this method mutates `array`.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to modify.
   * @param {...(number|number[])} [indexes] The indexes of elements to remove.
   * @returns {Array} Returns the new array of removed elements.
   * @example
   *
   * var array = ['a', 'b', 'c', 'd'];
   * var pulled = _.pullAt(array, [1, 3]);
   *
   * console.log(array);
   * // => ['a', 'c']
   *
   * console.log(pulled);
   * // => ['b', 'd']
   */
  var pullAt = flatRest(function(array, indexes) {
    var length = array == null ? 0 : array.length,
      result = baseAt(array, indexes)

    basePullAt(
      array,
      arrayMap(indexes, function(index) {
        return isIndex(index, length) ? +index : index
      }).sort(compareAscending)
    )

    return result
  })

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeFloor$2 = Math.floor,
    nativeRandom = Math.random

  /**
   * The base implementation of `_.random` without support for returning
   * floating-point numbers.
   *
   * @private
   * @param {number} lower The lower bound.
   * @param {number} upper The upper bound.
   * @returns {number} Returns the random number.
   */
  function baseRandom(lower, upper) {
    return lower + nativeFloor$2(nativeRandom() * (upper - lower + 1))
  }

  /** Built-in method references without a dependency on `root`. */
  var freeParseFloat = parseFloat

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin$9 = Math.min,
    nativeRandom$1 = Math.random

  /**
   * Produces a random number between the inclusive `lower` and `upper` bounds.
   * If only one argument is provided a number between `0` and the given number
   * is returned. If `floating` is `true`, or either `lower` or `upper` are
   * floats, a floating-point number is returned instead of an integer.
   *
   * **Note:** JavaScript follows the IEEE-754 standard for resolving
   * floating-point values which can produce unexpected results.
   *
   * @static
   * @memberOf _
   * @since 0.7.0
   * @category Number
   * @param {number} [lower=0] The lower bound.
   * @param {number} [upper=1] The upper bound.
   * @param {boolean} [floating] Specify returning a floating-point number.
   * @returns {number} Returns the random number.
   * @example
   *
   * _.random(0, 5);
   * // => an integer between 0 and 5
   *
   * _.random(5);
   * // => also an integer between 0 and 5
   *
   * _.random(5, true);
   * // => a floating-point number between 0 and 5
   *
   * _.random(1.2, 5.2);
   * // => a floating-point number between 1.2 and 5.2
   */
  function random(lower, upper, floating) {
    if (
      floating &&
      typeof floating != 'boolean' &&
      isIterateeCall(lower, upper, floating)
    ) {
      upper = floating = undefined
    }
    if (floating === undefined) {
      if (typeof upper == 'boolean') {
        floating = upper
        upper = undefined
      } else if (typeof lower == 'boolean') {
        floating = lower
        lower = undefined
      }
    }
    if (lower === undefined && upper === undefined) {
      lower = 0
      upper = 1
    } else {
      lower = toFinite(lower)
      if (upper === undefined) {
        upper = lower
        lower = 0
      } else {
        upper = toFinite(upper)
      }
    }
    if (lower > upper) {
      var temp = lower
      lower = upper
      upper = temp
    }
    if (floating || lower % 1 || upper % 1) {
      var rand = nativeRandom$1()
      return nativeMin$9(
        lower +
          rand *
            (upper - lower + freeParseFloat('1e-' + ((rand + '').length - 1))),
        upper
      )
    }
    return baseRandom(lower, upper)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeCeil$3 = Math.ceil,
    nativeMax$c = Math.max

  /**
   * The base implementation of `_.range` and `_.rangeRight` which doesn't
   * coerce arguments.
   *
   * @private
   * @param {number} start The start of the range.
   * @param {number} end The end of the range.
   * @param {number} step The value to increment or decrement by.
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Array} Returns the range of numbers.
   */
  function baseRange(start, end, step, fromRight) {
    var index = -1,
      length = nativeMax$c(nativeCeil$3((end - start) / (step || 1)), 0),
      result = Array(length)

    while (length--) {
      result[fromRight ? length : ++index] = start
      start += step
    }
    return result
  }

  /**
   * Creates a `_.range` or `_.rangeRight` function.
   *
   * @private
   * @param {boolean} [fromRight] Specify iterating from right to left.
   * @returns {Function} Returns the new range function.
   */
  function createRange(fromRight) {
    return function(start, end, step) {
      if (step && typeof step != 'number' && isIterateeCall(start, end, step)) {
        end = step = undefined
      }
      // Ensure the sign of `-0` is preserved.
      start = toFinite(start)
      if (end === undefined) {
        end = start
        start = 0
      } else {
        end = toFinite(end)
      }
      step = step === undefined ? (start < end ? 1 : -1) : toFinite(step)
      return baseRange(start, end, step, fromRight)
    }
  }

  /**
   * Creates an array of numbers (positive and/or negative) progressing from
   * `start` up to, but not including, `end`. A step of `-1` is used if a negative
   * `start` is specified without an `end` or `step`. If `end` is not specified,
   * it's set to `start` with `start` then set to `0`.
   *
   * **Note:** JavaScript follows the IEEE-754 standard for resolving
   * floating-point values which can produce unexpected results.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {number} [start=0] The start of the range.
   * @param {number} end The end of the range.
   * @param {number} [step=1] The value to increment or decrement by.
   * @returns {Array} Returns the range of numbers.
   * @see _.inRange, _.rangeRight
   * @example
   *
   * _.range(4);
   * // => [0, 1, 2, 3]
   *
   * _.range(-4);
   * // => [0, -1, -2, -3]
   *
   * _.range(1, 5);
   * // => [1, 2, 3, 4]
   *
   * _.range(0, 20, 5);
   * // => [0, 5, 10, 15]
   *
   * _.range(0, -4, -1);
   * // => [0, -1, -2, -3]
   *
   * _.range(1, 4, 0);
   * // => [1, 1, 1]
   *
   * _.range(0);
   * // => []
   */
  var range$1 = createRange()

  /**
   * This method is like `_.range` except that it populates values in
   * descending order.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {number} [start=0] The start of the range.
   * @param {number} end The end of the range.
   * @param {number} [step=1] The value to increment or decrement by.
   * @returns {Array} Returns the range of numbers.
   * @see _.inRange, _.range
   * @example
   *
   * _.rangeRight(4);
   * // => [3, 2, 1, 0]
   *
   * _.rangeRight(-4);
   * // => [-3, -2, -1, 0]
   *
   * _.rangeRight(1, 5);
   * // => [4, 3, 2, 1]
   *
   * _.rangeRight(0, 20, 5);
   * // => [15, 10, 5, 0]
   *
   * _.rangeRight(0, -4, -1);
   * // => [-3, -2, -1, 0]
   *
   * _.rangeRight(1, 4, 0);
   * // => [1, 1, 1]
   *
   * _.rangeRight(0);
   * // => []
   */
  var rangeRight = createRange(true)

  /** Used to compose bitmasks for function metadata. */
  var WRAP_REARG_FLAG$3 = 256

  /**
   * Creates a function that invokes `func` with arguments arranged according
   * to the specified `indexes` where the argument value at the first index is
   * provided as the first argument, the argument value at the second index is
   * provided as the second argument, and so on.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Function
   * @param {Function} func The function to rearrange arguments for.
   * @param {...(number|number[])} indexes The arranged argument indexes.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var rearged = _.rearg(function(a, b, c) {
   *   return [a, b, c];
   * }, [2, 0, 1]);
   *
   * rearged('b', 'c', 'a')
   * // => ['a', 'b', 'c']
   */
  var rearg = flatRest(function(func, indexes) {
    return createWrap(
      func,
      WRAP_REARG_FLAG$3,
      undefined,
      undefined,
      undefined,
      indexes
    )
  })

  /**
   * The base implementation of `_.reduce` and `_.reduceRight`, without support
   * for iteratee shorthands, which iterates over `collection` using `eachFunc`.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {*} accumulator The initial value.
   * @param {boolean} initAccum Specify using the first or last element of
   *  `collection` as the initial value.
   * @param {Function} eachFunc The function to iterate over `collection`.
   * @returns {*} Returns the accumulated value.
   */
  function baseReduce(collection, iteratee, accumulator, initAccum, eachFunc) {
    eachFunc(collection, function(value, index, collection) {
      accumulator = initAccum
        ? ((initAccum = false), value)
        : iteratee(accumulator, value, index, collection)
    })
    return accumulator
  }

  /**
   * Reduces `collection` to a value which is the accumulated result of running
   * each element in `collection` thru `iteratee`, where each successive
   * invocation is supplied the return value of the previous. If `accumulator`
   * is not given, the first element of `collection` is used as the initial
   * value. The iteratee is invoked with four arguments:
   * (accumulator, value, index|key, collection).
   *
   * Many lodash methods are guarded to work as iteratees for methods like
   * `_.reduce`, `_.reduceRight`, and `_.transform`.
   *
   * The guarded methods are:
   * `assign`, `defaults`, `defaultsDeep`, `includes`, `merge`, `orderBy`,
   * and `sortBy`
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @param {*} [accumulator] The initial value.
   * @returns {*} Returns the accumulated value.
   * @see _.reduceRight
   * @example
   *
   * _.reduce([1, 2], function(sum, n) {
   *   return sum + n;
   * }, 0);
   * // => 3
   *
   * _.reduce({ 'a': 1, 'b': 2, 'c': 1 }, function(result, value, key) {
   *   (result[value] || (result[value] = [])).push(key);
   *   return result;
   * }, {});
   * // => { '1': ['a', 'c'], '2': ['b'] } (iteration order is not guaranteed)
   */
  function reduce(collection, iteratee, accumulator) {
    var func = isArray(collection) ? arrayReduce : baseReduce,
      initAccum = arguments.length < 3

    return func(
      collection,
      baseIteratee(iteratee),
      accumulator,
      initAccum,
      baseEach
    )
  }

  /**
   * A specialized version of `_.reduceRight` for arrays without support for
   * iteratee shorthands.
   *
   * @private
   * @param {Array} [array] The array to iterate over.
   * @param {Function} iteratee The function invoked per iteration.
   * @param {*} [accumulator] The initial value.
   * @param {boolean} [initAccum] Specify using the last element of `array` as
   *  the initial value.
   * @returns {*} Returns the accumulated value.
   */
  function arrayReduceRight(array, iteratee, accumulator, initAccum) {
    var length = array == null ? 0 : array.length
    if (initAccum && length) {
      accumulator = array[--length]
    }
    while (length--) {
      accumulator = iteratee(accumulator, array[length], length, array)
    }
    return accumulator
  }

  /**
   * This method is like `_.reduce` except that it iterates over elements of
   * `collection` from right to left.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @param {*} [accumulator] The initial value.
   * @returns {*} Returns the accumulated value.
   * @see _.reduce
   * @example
   *
   * var array = [[0, 1], [2, 3], [4, 5]];
   *
   * _.reduceRight(array, function(flattened, other) {
   *   return flattened.concat(other);
   * }, []);
   * // => [4, 5, 2, 3, 0, 1]
   */
  function reduceRight(collection, iteratee, accumulator) {
    var func = isArray(collection) ? arrayReduceRight : baseReduce,
      initAccum = arguments.length < 3

    return func(
      collection,
      baseIteratee(iteratee),
      accumulator,
      initAccum,
      baseEachRight
    )
  }

  /**
   * The opposite of `_.filter`; this method returns the elements of `collection`
   * that `predicate` does **not** return truthy for.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the new filtered array.
   * @see _.filter
   * @example
   *
   * var users = [
   *   { 'user': 'barney', 'age': 36, 'active': false },
   *   { 'user': 'fred',   'age': 40, 'active': true }
   * ];
   *
   * _.reject(users, function(o) { return !o.active; });
   * // => objects for ['fred']
   *
   * // The `_.matches` iteratee shorthand.
   * _.reject(users, { 'age': 40, 'active': true });
   * // => objects for ['barney']
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.reject(users, ['active', false]);
   * // => objects for ['fred']
   *
   * // The `_.property` iteratee shorthand.
   * _.reject(users, 'active');
   * // => objects for ['barney']
   */
  function reject(collection, predicate) {
    var func = isArray(collection) ? arrayFilter : baseFilter
    return func(collection, negate(baseIteratee(predicate)))
  }

  /**
   * Removes all elements from `array` that `predicate` returns truthy for
   * and returns an array of the removed elements. The predicate is invoked
   * with three arguments: (value, index, array).
   *
   * **Note:** Unlike `_.filter`, this method mutates `array`. Use `_.pull`
   * to pull elements from an array by value.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Array
   * @param {Array} array The array to modify.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the new array of removed elements.
   * @example
   *
   * var array = [1, 2, 3, 4];
   * var evens = _.remove(array, function(n) {
   *   return n % 2 == 0;
   * });
   *
   * console.log(array);
   * // => [1, 3]
   *
   * console.log(evens);
   * // => [2, 4]
   */
  function remove(array, predicate) {
    var result = []
    if (!(array && array.length)) {
      return result
    }
    var index = -1,
      indexes = [],
      length = array.length

    predicate = baseIteratee(predicate)
    while (++index < length) {
      var value = array[index]
      if (predicate(value, index, array)) {
        result.push(value)
        indexes.push(index)
      }
    }
    basePullAt(array, indexes)
    return result
  }

  /**
   * Repeats the given string `n` times.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to repeat.
   * @param {number} [n=1] The number of times to repeat the string.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {string} Returns the repeated string.
   * @example
   *
   * _.repeat('*', 3);
   * // => '***'
   *
   * _.repeat('abc', 2);
   * // => 'abcabc'
   *
   * _.repeat('abc', 0);
   * // => ''
   */
  function repeat(string, n, guard) {
    if (guard ? isIterateeCall(string, n, guard) : n === undefined) {
      n = 1
    } else {
      n = toInteger(n)
    }
    return baseRepeat(toString(string), n)
  }

  /**
   * Replaces matches for `pattern` in `string` with `replacement`.
   *
   * **Note:** This method is based on
   * [`String#replace`](https://mdn.io/String/replace).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to modify.
   * @param {RegExp|string} pattern The pattern to replace.
   * @param {Function|string} replacement The match replacement.
   * @returns {string} Returns the modified string.
   * @example
   *
   * _.replace('Hi Fred', 'Fred', 'Barney');
   * // => 'Hi Barney'
   */
  function replace() {
    var args = arguments,
      string = toString(args[0])

    return args.length < 3 ? string : string.replace(args[1], args[2])
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$9 = 'Expected a function'

  /**
   * Creates a function that invokes `func` with the `this` binding of the
   * created function and arguments from `start` and beyond provided as
   * an array.
   *
   * **Note:** This method is based on the
   * [rest parameter](https://mdn.io/rest_parameters).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Function
   * @param {Function} func The function to apply a rest parameter to.
   * @param {number} [start=func.length-1] The start position of the rest parameter.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var say = _.rest(function(what, names) {
   *   return what + ' ' + _.initial(names).join(', ') +
   *     (_.size(names) > 1 ? ', & ' : '') + _.last(names);
   * });
   *
   * say('hello', 'fred', 'barney', 'pebbles');
   * // => 'hello fred, barney, & pebbles'
   */
  function rest(func, start) {
    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$9)
    }
    start = start === undefined ? start : toInteger(start)
    return baseRest(func, start)
  }

  /**
   * This method is like `_.get` except that if the resolved value is a
   * function it's invoked with the `this` binding of its parent object and
   * its result is returned.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Object
   * @param {Object} object The object to query.
   * @param {Array|string} path The path of the property to resolve.
   * @param {*} [defaultValue] The value returned for `undefined` resolved values.
   * @returns {*} Returns the resolved value.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c1': 3, 'c2': _.constant(4) } }] };
   *
   * _.result(object, 'a[0].b.c1');
   * // => 3
   *
   * _.result(object, 'a[0].b.c2');
   * // => 4
   *
   * _.result(object, 'a[0].b.c3', 'default');
   * // => 'default'
   *
   * _.result(object, 'a[0].b.c3', _.constant('default'));
   * // => 'default'
   */
  function result(object, path, defaultValue) {
    path = castPath(path, object)

    var index = -1,
      length = path.length

    // Ensure the loop is entered when path is empty.
    if (!length) {
      length = 1
      object = undefined
    }
    while (++index < length) {
      var value = object == null ? undefined : object[toKey(path[index])]
      if (value === undefined) {
        index = length
        value = defaultValue
      }
      object = isFunction(value) ? value.call(object) : value
    }
    return object
  }

  /** Used for built-in method references. */
  var arrayProto$4 = Array.prototype

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeReverse = arrayProto$4.reverse

  /**
   * Reverses `array` so that the first element becomes the last, the second
   * element becomes the second to last, and so on.
   *
   * **Note:** This method mutates `array` and is based on
   * [`Array#reverse`](https://mdn.io/Array/reverse).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to modify.
   * @returns {Array} Returns `array`.
   * @example
   *
   * var array = [1, 2, 3];
   *
   * _.reverse(array);
   * // => [3, 2, 1]
   *
   * console.log(array);
   * // => [3, 2, 1]
   */
  function reverse(array) {
    return array == null ? array : nativeReverse.call(array)
  }

  /**
   * Computes `number` rounded to `precision`.
   *
   * @static
   * @memberOf _
   * @since 3.10.0
   * @category Math
   * @param {number} number The number to round.
   * @param {number} [precision=0] The precision to round to.
   * @returns {number} Returns the rounded number.
   * @example
   *
   * _.round(4.006);
   * // => 4
   *
   * _.round(4.006, 2);
   * // => 4.01
   *
   * _.round(4060, -2);
   * // => 4100
   */
  var round = createRound('round')

  /**
   * A specialized version of `_.sample` for arrays.
   *
   * @private
   * @param {Array} array The array to sample.
   * @returns {*} Returns the random element.
   */
  function arraySample(array) {
    var length = array.length
    return length ? array[baseRandom(0, length - 1)] : undefined
  }

  /**
   * The base implementation of `_.sample`.
   *
   * @private
   * @param {Array|Object} collection The collection to sample.
   * @returns {*} Returns the random element.
   */
  function baseSample(collection) {
    return arraySample(values(collection))
  }

  /**
   * Gets a random element from `collection`.
   *
   * @static
   * @memberOf _
   * @since 2.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to sample.
   * @returns {*} Returns the random element.
   * @example
   *
   * _.sample([1, 2, 3, 4]);
   * // => 2
   */
  function sample(collection) {
    var func = isArray(collection) ? arraySample : baseSample
    return func(collection)
  }

  /**
   * A specialized version of `_.shuffle` which mutates and sets the size of `array`.
   *
   * @private
   * @param {Array} array The array to shuffle.
   * @param {number} [size=array.length] The size of `array`.
   * @returns {Array} Returns `array`.
   */
  function shuffleSelf(array, size) {
    var index = -1,
      length = array.length,
      lastIndex = length - 1

    size = size === undefined ? length : size
    while (++index < size) {
      var rand = baseRandom(index, lastIndex),
        value = array[rand]

      array[rand] = array[index]
      array[index] = value
    }
    array.length = size
    return array
  }

  /**
   * A specialized version of `_.sampleSize` for arrays.
   *
   * @private
   * @param {Array} array The array to sample.
   * @param {number} n The number of elements to sample.
   * @returns {Array} Returns the random elements.
   */
  function arraySampleSize(array, n) {
    return shuffleSelf(copyArray(array), baseClamp(n, 0, array.length))
  }

  /**
   * The base implementation of `_.sampleSize` without param guards.
   *
   * @private
   * @param {Array|Object} collection The collection to sample.
   * @param {number} n The number of elements to sample.
   * @returns {Array} Returns the random elements.
   */
  function baseSampleSize(collection, n) {
    var array = values(collection)
    return shuffleSelf(array, baseClamp(n, 0, array.length))
  }

  /**
   * Gets `n` random elements at unique keys from `collection` up to the
   * size of `collection`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Collection
   * @param {Array|Object} collection The collection to sample.
   * @param {number} [n=1] The number of elements to sample.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the random elements.
   * @example
   *
   * _.sampleSize([1, 2, 3], 2);
   * // => [3, 1]
   *
   * _.sampleSize([1, 2, 3], 4);
   * // => [2, 3, 1]
   */
  function sampleSize(collection, n, guard) {
    if (guard ? isIterateeCall(collection, n, guard) : n === undefined) {
      n = 1
    } else {
      n = toInteger(n)
    }
    var func = isArray(collection) ? arraySampleSize : baseSampleSize
    return func(collection, n)
  }

  /**
   * Sets the value at `path` of `object`. If a portion of `path` doesn't exist,
   * it's created. Arrays are created for missing index properties while objects
   * are created for all other missing properties. Use `_.setWith` to customize
   * `path` creation.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 3.7.0
   * @category Object
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to set.
   * @param {*} value The value to set.
   * @returns {Object} Returns `object`.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 3 } }] };
   *
   * _.set(object, 'a[0].b.c', 4);
   * console.log(object.a[0].b.c);
   * // => 4
   *
   * _.set(object, ['x', '0', 'y', 'z'], 5);
   * console.log(object.x[0].y.z);
   * // => 5
   */
  function set(object, path, value) {
    return object == null ? object : baseSet(object, path, value)
  }

  /**
   * This method is like `_.set` except that it accepts `customizer` which is
   * invoked to produce the objects of `path`.  If `customizer` returns `undefined`
   * path creation is handled by the method instead. The `customizer` is invoked
   * with three arguments: (nsValue, key, nsObject).
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to set.
   * @param {*} value The value to set.
   * @param {Function} [customizer] The function to customize assigned values.
   * @returns {Object} Returns `object`.
   * @example
   *
   * var object = {};
   *
   * _.setWith(object, '[0][1]', 'a', Object);
   * // => { '0': { '1': 'a' } }
   */
  function setWith(object, path, value, customizer) {
    customizer = typeof customizer == 'function' ? customizer : undefined
    return object == null ? object : baseSet(object, path, value, customizer)
  }

  /**
   * A specialized version of `_.shuffle` for arrays.
   *
   * @private
   * @param {Array} array The array to shuffle.
   * @returns {Array} Returns the new shuffled array.
   */
  function arrayShuffle(array) {
    return shuffleSelf(copyArray(array))
  }

  /**
   * The base implementation of `_.shuffle`.
   *
   * @private
   * @param {Array|Object} collection The collection to shuffle.
   * @returns {Array} Returns the new shuffled array.
   */
  function baseShuffle(collection) {
    return shuffleSelf(values(collection))
  }

  /**
   * Creates an array of shuffled values, using a version of the
   * [Fisher-Yates shuffle](https://en.wikipedia.org/wiki/Fisher-Yates_shuffle).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to shuffle.
   * @returns {Array} Returns the new shuffled array.
   * @example
   *
   * _.shuffle([1, 2, 3, 4]);
   * // => [4, 1, 3, 2]
   */
  function shuffle(collection) {
    var func = isArray(collection) ? arrayShuffle : baseShuffle
    return func(collection)
  }

  /** `Object#toString` result references. */
  var mapTag$9 = '[object Map]',
    setTag$9 = '[object Set]'

  /**
   * Gets the size of `collection` by returning its length for array-like
   * values or the number of own enumerable string keyed properties for objects.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object|string} collection The collection to inspect.
   * @returns {number} Returns the collection size.
   * @example
   *
   * _.size([1, 2, 3]);
   * // => 3
   *
   * _.size({ 'a': 1, 'b': 2 });
   * // => 2
   *
   * _.size('pebbles');
   * // => 7
   */
  function size(collection) {
    if (collection == null) {
      return 0
    }
    if (isArrayLike(collection)) {
      return isString(collection) ? stringSize(collection) : collection.length
    }
    var tag = getTag$1(collection)
    if (tag == mapTag$9 || tag == setTag$9) {
      return collection.size
    }
    return baseKeys(collection).length
  }

  /**
   * Creates a slice of `array` from `start` up to, but not including, `end`.
   *
   * **Note:** This method is used instead of
   * [`Array#slice`](https://mdn.io/Array/slice) to ensure dense arrays are
   * returned.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to slice.
   * @param {number} [start=0] The start position.
   * @param {number} [end=array.length] The end position.
   * @returns {Array} Returns the slice of `array`.
   */
  function slice(array, start, end) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return []
    }
    if (end && typeof end != 'number' && isIterateeCall(array, start, end)) {
      start = 0
      end = length
    } else {
      start = start == null ? 0 : toInteger(start)
      end = end === undefined ? length : toInteger(end)
    }
    return baseSlice(array, start, end)
  }

  /**
   * Converts `string` to
   * [snake case](https://en.wikipedia.org/wiki/Snake_case).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the snake cased string.
   * @example
   *
   * _.snakeCase('Foo Bar');
   * // => 'foo_bar'
   *
   * _.snakeCase('fooBar');
   * // => 'foo_bar'
   *
   * _.snakeCase('--FOO-BAR--');
   * // => 'foo_bar'
   */
  var snakeCase = createCompounder(function(result, word, index) {
    return result + (index ? '_' : '') + word.toLowerCase()
  })

  /**
   * The base implementation of `_.some` without support for iteratee shorthands.
   *
   * @private
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} predicate The function invoked per iteration.
   * @returns {boolean} Returns `true` if any element passes the predicate check,
   *  else `false`.
   */
  function baseSome(collection, predicate) {
    var result

    baseEach(collection, function(value, index, collection) {
      result = predicate(value, index, collection)
      return !result
    })
    return !!result
  }

  /**
   * Checks if `predicate` returns truthy for **any** element of `collection`.
   * Iteration is stopped once `predicate` returns truthy. The predicate is
   * invoked with three arguments: (value, index|key, collection).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {boolean} Returns `true` if any element passes the predicate check,
   *  else `false`.
   * @example
   *
   * _.some([null, 0, 'yes', false], Boolean);
   * // => true
   *
   * var users = [
   *   { 'user': 'barney', 'active': true },
   *   { 'user': 'fred',   'active': false }
   * ];
   *
   * // The `_.matches` iteratee shorthand.
   * _.some(users, { 'user': 'barney', 'active': false });
   * // => false
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.some(users, ['active', false]);
   * // => true
   *
   * // The `_.property` iteratee shorthand.
   * _.some(users, 'active');
   * // => true
   */
  function some(collection, predicate, guard) {
    var func = isArray(collection) ? arraySome : baseSome
    if (guard && isIterateeCall(collection, predicate, guard)) {
      predicate = undefined
    }
    return func(collection, baseIteratee(predicate))
  }

  /**
   * Creates an array of elements, sorted in ascending order by the results of
   * running each element in a collection thru each iteratee. This method
   * performs a stable sort, that is, it preserves the original sort order of
   * equal elements. The iteratees are invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Collection
   * @param {Array|Object} collection The collection to iterate over.
   * @param {...(Function|Function[])} [iteratees=[_.identity]]
   *  The iteratees to sort by.
   * @returns {Array} Returns the new sorted array.
   * @example
   *
   * var users = [
   *   { 'user': 'fred',   'age': 48 },
   *   { 'user': 'barney', 'age': 36 },
   *   { 'user': 'fred',   'age': 40 },
   *   { 'user': 'barney', 'age': 34 }
   * ];
   *
   * _.sortBy(users, [function(o) { return o.user; }]);
   * // => objects for [['barney', 36], ['barney', 34], ['fred', 48], ['fred', 40]]
   *
   * _.sortBy(users, ['user', 'age']);
   * // => objects for [['barney', 34], ['barney', 36], ['fred', 40], ['fred', 48]]
   */
  var sortBy = baseRest(function(collection, iteratees) {
    if (collection == null) {
      return []
    }
    var length = iteratees.length
    if (length > 1 && isIterateeCall(collection, iteratees[0], iteratees[1])) {
      iteratees = []
    } else if (
      length > 2 &&
      isIterateeCall(iteratees[0], iteratees[1], iteratees[2])
    ) {
      iteratees = [iteratees[0]]
    }
    return baseOrderBy(collection, baseFlatten(iteratees, 1), [])
  })

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH$2 = 4294967295,
    MAX_ARRAY_INDEX = MAX_ARRAY_LENGTH$2 - 1

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeFloor$3 = Math.floor,
    nativeMin$a = Math.min

  /**
   * The base implementation of `_.sortedIndexBy` and `_.sortedLastIndexBy`
   * which invokes `iteratee` for `value` and each element of `array` to compute
   * their sort ranking. The iteratee is invoked with one argument; (value).
   *
   * @private
   * @param {Array} array The sorted array to inspect.
   * @param {*} value The value to evaluate.
   * @param {Function} iteratee The iteratee invoked per element.
   * @param {boolean} [retHighest] Specify returning the highest qualified index.
   * @returns {number} Returns the index at which `value` should be inserted
   *  into `array`.
   */
  function baseSortedIndexBy(array, value, iteratee, retHighest) {
    value = iteratee(value)

    var low = 0,
      high = array == null ? 0 : array.length,
      valIsNaN = value !== value,
      valIsNull = value === null,
      valIsSymbol = isSymbol(value),
      valIsUndefined = value === undefined

    while (low < high) {
      var mid = nativeFloor$3((low + high) / 2),
        computed = iteratee(array[mid]),
        othIsDefined = computed !== undefined,
        othIsNull = computed === null,
        othIsReflexive = computed === computed,
        othIsSymbol = isSymbol(computed)

      if (valIsNaN) {
        var setLow = retHighest || othIsReflexive
      } else if (valIsUndefined) {
        setLow = othIsReflexive && (retHighest || othIsDefined)
      } else if (valIsNull) {
        setLow = othIsReflexive && othIsDefined && (retHighest || !othIsNull)
      } else if (valIsSymbol) {
        setLow =
          othIsReflexive &&
          othIsDefined &&
          !othIsNull &&
          (retHighest || !othIsSymbol)
      } else if (othIsNull || othIsSymbol) {
        setLow = false
      } else {
        setLow = retHighest ? computed <= value : computed < value
      }
      if (setLow) {
        low = mid + 1
      } else {
        high = mid
      }
    }
    return nativeMin$a(high, MAX_ARRAY_INDEX)
  }

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH$3 = 4294967295,
    HALF_MAX_ARRAY_LENGTH = MAX_ARRAY_LENGTH$3 >>> 1

  /**
   * The base implementation of `_.sortedIndex` and `_.sortedLastIndex` which
   * performs a binary search of `array` to determine the index at which `value`
   * should be inserted into `array` in order to maintain its sort order.
   *
   * @private
   * @param {Array} array The sorted array to inspect.
   * @param {*} value The value to evaluate.
   * @param {boolean} [retHighest] Specify returning the highest qualified index.
   * @returns {number} Returns the index at which `value` should be inserted
   *  into `array`.
   */
  function baseSortedIndex(array, value, retHighest) {
    var low = 0,
      high = array == null ? low : array.length

    if (
      typeof value == 'number' &&
      value === value &&
      high <= HALF_MAX_ARRAY_LENGTH
    ) {
      while (low < high) {
        var mid = (low + high) >>> 1,
          computed = array[mid]

        if (
          computed !== null &&
          !isSymbol(computed) &&
          (retHighest ? computed <= value : computed < value)
        ) {
          low = mid + 1
        } else {
          high = mid
        }
      }
      return high
    }
    return baseSortedIndexBy(array, value, identity, retHighest)
  }

  /**
   * Uses a binary search to determine the lowest index at which `value`
   * should be inserted into `array` in order to maintain its sort order.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The sorted array to inspect.
   * @param {*} value The value to evaluate.
   * @returns {number} Returns the index at which `value` should be inserted
   *  into `array`.
   * @example
   *
   * _.sortedIndex([30, 50], 40);
   * // => 1
   */
  function sortedIndex(array, value) {
    return baseSortedIndex(array, value)
  }

  /**
   * This method is like `_.sortedIndex` except that it accepts `iteratee`
   * which is invoked for `value` and each element of `array` to compute their
   * sort ranking. The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The sorted array to inspect.
   * @param {*} value The value to evaluate.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {number} Returns the index at which `value` should be inserted
   *  into `array`.
   * @example
   *
   * var objects = [{ 'x': 4 }, { 'x': 5 }];
   *
   * _.sortedIndexBy(objects, { 'x': 4 }, function(o) { return o.x; });
   * // => 0
   *
   * // The `_.property` iteratee shorthand.
   * _.sortedIndexBy(objects, { 'x': 4 }, 'x');
   * // => 0
   */
  function sortedIndexBy(array, value, iteratee) {
    return baseSortedIndexBy(array, value, baseIteratee(iteratee))
  }

  /**
   * This method is like `_.indexOf` except that it performs a binary
   * search on a sorted `array`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @returns {number} Returns the index of the matched value, else `-1`.
   * @example
   *
   * _.sortedIndexOf([4, 5, 5, 5, 6], 5);
   * // => 1
   */
  function sortedIndexOf(array, value) {
    var length = array == null ? 0 : array.length
    if (length) {
      var index = baseSortedIndex(array, value)
      if (index < length && eq$1(array[index], value)) {
        return index
      }
    }
    return -1
  }

  /**
   * This method is like `_.sortedIndex` except that it returns the highest
   * index at which `value` should be inserted into `array` in order to
   * maintain its sort order.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The sorted array to inspect.
   * @param {*} value The value to evaluate.
   * @returns {number} Returns the index at which `value` should be inserted
   *  into `array`.
   * @example
   *
   * _.sortedLastIndex([4, 5, 5, 5, 6], 5);
   * // => 4
   */
  function sortedLastIndex(array, value) {
    return baseSortedIndex(array, value, true)
  }

  /**
   * This method is like `_.sortedLastIndex` except that it accepts `iteratee`
   * which is invoked for `value` and each element of `array` to compute their
   * sort ranking. The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The sorted array to inspect.
   * @param {*} value The value to evaluate.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {number} Returns the index at which `value` should be inserted
   *  into `array`.
   * @example
   *
   * var objects = [{ 'x': 4 }, { 'x': 5 }];
   *
   * _.sortedLastIndexBy(objects, { 'x': 4 }, function(o) { return o.x; });
   * // => 1
   *
   * // The `_.property` iteratee shorthand.
   * _.sortedLastIndexBy(objects, { 'x': 4 }, 'x');
   * // => 1
   */
  function sortedLastIndexBy(array, value, iteratee) {
    return baseSortedIndexBy(array, value, baseIteratee(iteratee), true)
  }

  /**
   * This method is like `_.lastIndexOf` except that it performs a binary
   * search on a sorted `array`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {*} value The value to search for.
   * @returns {number} Returns the index of the matched value, else `-1`.
   * @example
   *
   * _.sortedLastIndexOf([4, 5, 5, 5, 6], 5);
   * // => 3
   */
  function sortedLastIndexOf(array, value) {
    var length = array == null ? 0 : array.length
    if (length) {
      var index = baseSortedIndex(array, value, true) - 1
      if (eq$1(array[index], value)) {
        return index
      }
    }
    return -1
  }

  /**
   * The base implementation of `_.sortedUniq` and `_.sortedUniqBy` without
   * support for iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @returns {Array} Returns the new duplicate free array.
   */
  function baseSortedUniq(array, iteratee) {
    var index = -1,
      length = array.length,
      resIndex = 0,
      result = []

    while (++index < length) {
      var value = array[index],
        computed = iteratee ? iteratee(value) : value

      if (!index || !eq$1(computed, seen)) {
        var seen = computed
        result[resIndex++] = value === 0 ? 0 : value
      }
    }
    return result
  }

  /**
   * This method is like `_.uniq` except that it's designed and optimized
   * for sorted arrays.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @returns {Array} Returns the new duplicate free array.
   * @example
   *
   * _.sortedUniq([1, 1, 2]);
   * // => [1, 2]
   */
  function sortedUniq(array) {
    return array && array.length ? baseSortedUniq(array) : []
  }

  /**
   * This method is like `_.uniqBy` except that it's designed and optimized
   * for sorted arrays.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @returns {Array} Returns the new duplicate free array.
   * @example
   *
   * _.sortedUniqBy([1.1, 1.2, 2.3, 2.4], Math.floor);
   * // => [1.1, 2.3]
   */
  function sortedUniqBy(array, iteratee) {
    return array && array.length
      ? baseSortedUniq(array, baseIteratee(iteratee))
      : []
  }

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH$4 = 4294967295

  /**
   * Splits `string` by `separator`.
   *
   * **Note:** This method is based on
   * [`String#split`](https://mdn.io/String/split).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to split.
   * @param {RegExp|string} separator The separator pattern to split by.
   * @param {number} [limit] The length to truncate results to.
   * @returns {Array} Returns the string segments.
   * @example
   *
   * _.split('a-b-c', '-', 2);
   * // => ['a', 'b']
   */
  function split(string, separator, limit) {
    if (
      limit &&
      typeof limit != 'number' &&
      isIterateeCall(string, separator, limit)
    ) {
      separator = limit = undefined
    }
    limit = limit === undefined ? MAX_ARRAY_LENGTH$4 : limit >>> 0
    if (!limit) {
      return []
    }
    string = toString(string)
    if (
      string &&
      (typeof separator == 'string' ||
        (separator != null && !isRegExp(separator)))
    ) {
      separator = baseToString(separator)
      if (!separator && hasUnicode(string)) {
        return castSlice(stringToArray(string), 0, limit)
      }
    }
    return string.split(separator, limit)
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$a = 'Expected a function'

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$d = Math.max

  /**
   * Creates a function that invokes `func` with the `this` binding of the
   * create function and an array of arguments much like
   * [`Function#apply`](http://www.ecma-international.org/ecma-262/7.0/#sec-function.prototype.apply).
   *
   * **Note:** This method is based on the
   * [spread operator](https://mdn.io/spread_operator).
   *
   * @static
   * @memberOf _
   * @since 3.2.0
   * @category Function
   * @param {Function} func The function to spread arguments over.
   * @param {number} [start=0] The start position of the spread.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var say = _.spread(function(who, what) {
   *   return who + ' says ' + what;
   * });
   *
   * say(['fred', 'hello']);
   * // => 'fred says hello'
   *
   * var numbers = Promise.all([
   *   Promise.resolve(40),
   *   Promise.resolve(36)
   * ]);
   *
   * numbers.then(_.spread(function(x, y) {
   *   return x + y;
   * }));
   * // => a Promise of 76
   */
  function spread(func, start) {
    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$a)
    }
    start = start == null ? 0 : nativeMax$d(toInteger(start), 0)
    return baseRest(function(args) {
      var array = args[start],
        otherArgs = castSlice(args, 0, start)

      if (array) {
        arrayPush(otherArgs, array)
      }
      return apply(func, this, otherArgs)
    })
  }

  /**
   * Converts `string` to
   * [start case](https://en.wikipedia.org/wiki/Letter_case#Stylistic_or_specialised_usage).
   *
   * @static
   * @memberOf _
   * @since 3.1.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the start cased string.
   * @example
   *
   * _.startCase('--foo-bar--');
   * // => 'Foo Bar'
   *
   * _.startCase('fooBar');
   * // => 'Foo Bar'
   *
   * _.startCase('__FOO_BAR__');
   * // => 'FOO BAR'
   */
  var startCase = createCompounder(function(result, word, index) {
    return result + (index ? ' ' : '') + upperFirst(word)
  })

  /**
   * Checks if `string` starts with the given target string.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to inspect.
   * @param {string} [target] The string to search for.
   * @param {number} [position=0] The position to search from.
   * @returns {boolean} Returns `true` if `string` starts with `target`,
   *  else `false`.
   * @example
   *
   * _.startsWith('abc', 'a');
   * // => true
   *
   * _.startsWith('abc', 'b');
   * // => false
   *
   * _.startsWith('abc', 'b', 1);
   * // => true
   */
  function startsWith(string, target, position) {
    string = toString(string)
    position =
      position == null ? 0 : baseClamp(toInteger(position), 0, string.length)

    target = baseToString(target)
    return string.slice(position, position + target.length) == target
  }

  /**
   * This method returns a new empty object.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {Object} Returns the new empty object.
   * @example
   *
   * var objects = _.times(2, _.stubObject);
   *
   * console.log(objects);
   * // => [{}, {}]
   *
   * console.log(objects[0] === objects[1]);
   * // => false
   */
  function stubObject() {
    return {}
  }

  /**
   * This method returns an empty string.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {string} Returns the empty string.
   * @example
   *
   * _.times(2, _.stubString);
   * // => ['', '']
   */
  function stubString() {
    return ''
  }

  /**
   * This method returns `true`.
   *
   * @static
   * @memberOf _
   * @since 4.13.0
   * @category Util
   * @returns {boolean} Returns `true`.
   * @example
   *
   * _.times(2, _.stubTrue);
   * // => [true, true]
   */
  function stubTrue() {
    return true
  }

  /**
   * Subtract two numbers.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Math
   * @param {number} minuend The first number in a subtraction.
   * @param {number} subtrahend The second number in a subtraction.
   * @returns {number} Returns the difference.
   * @example
   *
   * _.subtract(6, 4);
   * // => 2
   */
  var subtract$1 = createMathOperation(function(minuend, subtrahend) {
    return minuend - subtrahend
  }, 0)

  /**
   * Computes the sum of the values in `array`.
   *
   * @static
   * @memberOf _
   * @since 3.4.0
   * @category Math
   * @param {Array} array The array to iterate over.
   * @returns {number} Returns the sum.
   * @example
   *
   * _.sum([4, 2, 8, 6]);
   * // => 20
   */
  function sum(array) {
    return array && array.length ? baseSum(array, identity) : 0
  }

  /**
   * This method is like `_.sum` except that it accepts `iteratee` which is
   * invoked for each element in `array` to generate the value to be summed.
   * The iteratee is invoked with one argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Math
   * @param {Array} array The array to iterate over.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {number} Returns the sum.
   * @example
   *
   * var objects = [{ 'n': 4 }, { 'n': 2 }, { 'n': 8 }, { 'n': 6 }];
   *
   * _.sumBy(objects, function(o) { return o.n; });
   * // => 20
   *
   * // The `_.property` iteratee shorthand.
   * _.sumBy(objects, 'n');
   * // => 20
   */
  function sumBy(array, iteratee) {
    return array && array.length ? baseSum(array, baseIteratee(iteratee)) : 0
  }

  /**
   * Gets all but the first element of `array`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * _.tail([1, 2, 3]);
   * // => [2, 3]
   */
  function tail(array) {
    var length = array == null ? 0 : array.length
    return length ? baseSlice(array, 1, length) : []
  }

  /**
   * Creates a slice of `array` with `n` elements taken from the beginning.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {number} [n=1] The number of elements to take.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * _.take([1, 2, 3]);
   * // => [1]
   *
   * _.take([1, 2, 3], 2);
   * // => [1, 2]
   *
   * _.take([1, 2, 3], 5);
   * // => [1, 2, 3]
   *
   * _.take([1, 2, 3], 0);
   * // => []
   */
  function take(array, n, guard) {
    if (!(array && array.length)) {
      return []
    }
    n = guard || n === undefined ? 1 : toInteger(n)
    return baseSlice(array, 0, n < 0 ? 0 : n)
  }

  /**
   * Creates a slice of `array` with `n` elements taken from the end.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {number} [n=1] The number of elements to take.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * _.takeRight([1, 2, 3]);
   * // => [3]
   *
   * _.takeRight([1, 2, 3], 2);
   * // => [2, 3]
   *
   * _.takeRight([1, 2, 3], 5);
   * // => [1, 2, 3]
   *
   * _.takeRight([1, 2, 3], 0);
   * // => []
   */
  function takeRight(array, n, guard) {
    var length = array == null ? 0 : array.length
    if (!length) {
      return []
    }
    n = guard || n === undefined ? 1 : toInteger(n)
    n = length - n
    return baseSlice(array, n < 0 ? 0 : n, length)
  }

  /**
   * Creates a slice of `array` with elements taken from the end. Elements are
   * taken until `predicate` returns falsey. The predicate is invoked with
   * three arguments: (value, index, array).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': true },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': false }
   * ];
   *
   * _.takeRightWhile(users, function(o) { return !o.active; });
   * // => objects for ['fred', 'pebbles']
   *
   * // The `_.matches` iteratee shorthand.
   * _.takeRightWhile(users, { 'user': 'pebbles', 'active': false });
   * // => objects for ['pebbles']
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.takeRightWhile(users, ['active', false]);
   * // => objects for ['fred', 'pebbles']
   *
   * // The `_.property` iteratee shorthand.
   * _.takeRightWhile(users, 'active');
   * // => []
   */
  function takeRightWhile(array, predicate) {
    return array && array.length
      ? baseWhile(array, baseIteratee(predicate), false, true)
      : []
  }

  /**
   * Creates a slice of `array` with elements taken from the beginning. Elements
   * are taken until `predicate` returns falsey. The predicate is invoked with
   * three arguments: (value, index, array).
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Array
   * @param {Array} array The array to query.
   * @param {Function} [predicate=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the slice of `array`.
   * @example
   *
   * var users = [
   *   { 'user': 'barney',  'active': false },
   *   { 'user': 'fred',    'active': false },
   *   { 'user': 'pebbles', 'active': true }
   * ];
   *
   * _.takeWhile(users, function(o) { return !o.active; });
   * // => objects for ['barney', 'fred']
   *
   * // The `_.matches` iteratee shorthand.
   * _.takeWhile(users, { 'user': 'barney', 'active': false });
   * // => objects for ['barney']
   *
   * // The `_.matchesProperty` iteratee shorthand.
   * _.takeWhile(users, ['active', false]);
   * // => objects for ['barney', 'fred']
   *
   * // The `_.property` iteratee shorthand.
   * _.takeWhile(users, 'active');
   * // => []
   */
  function takeWhile(array, predicate) {
    return array && array.length
      ? baseWhile(array, baseIteratee(predicate))
      : []
  }

  /**
   * This method invokes `interceptor` and returns `value`. The interceptor
   * is invoked with one argument; (value). The purpose of this method is to
   * "tap into" a method chain sequence in order to modify intermediate results.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Seq
   * @param {*} value The value to provide to `interceptor`.
   * @param {Function} interceptor The function to invoke.
   * @returns {*} Returns `value`.
   * @example
   *
   * _([1, 2, 3])
   *  .tap(function(array) {
   *    // Mutate input array.
   *    array.pop();
   *  })
   *  .reverse()
   *  .value();
   * // => [2, 1]
   */
  function tap(value, interceptor) {
    interceptor(value)
    return value
  }

  /** Used for built-in method references. */
  var objectProto$q = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$n = objectProto$q.hasOwnProperty

  /**
   * Used by `_.defaults` to customize its `_.assignIn` use to assign properties
   * of source objects to the destination object for all destination properties
   * that resolve to `undefined`.
   *
   * @private
   * @param {*} objValue The destination value.
   * @param {*} srcValue The source value.
   * @param {string} key The key of the property to assign.
   * @param {Object} object The parent object of `objValue`.
   * @returns {*} Returns the value to assign.
   */
  function customDefaultsAssignIn(objValue, srcValue, key, object) {
    if (
      objValue === undefined ||
      (eq$1(objValue, objectProto$q[key]) &&
        !hasOwnProperty$n.call(object, key))
    ) {
      return srcValue
    }
    return objValue
  }

  /** Used to escape characters for inclusion in compiled string literals. */
  var stringEscapes = {
    '\\': '\\',
    "'": "'",
    '\n': 'n',
    '\r': 'r',
    '\u2028': 'u2028',
    '\u2029': 'u2029',
  }

  /**
   * Used by `_.template` to escape characters for inclusion in compiled string literals.
   *
   * @private
   * @param {string} chr The matched character to escape.
   * @returns {string} Returns the escaped character.
   */
  function escapeStringChar(chr) {
    return '\\' + stringEscapes[chr]
  }

  /** Used to match template delimiters. */
  var reInterpolate = /<%=([\s\S]+?)%>/g

  /** Used to match template delimiters. */
  var reEscape = /<%-([\s\S]+?)%>/g

  /** Used to match template delimiters. */
  var reEvaluate = /<%([\s\S]+?)%>/g

  /**
   * By default, the template delimiters used by lodash are like those in
   * embedded Ruby (ERB) as well as ES2015 template strings. Change the
   * following template settings to use alternative delimiters.
   *
   * @static
   * @memberOf _
   * @type {Object}
   */
  var templateSettings = {
    /**
     * Used to detect `data` property values to be HTML-escaped.
     *
     * @memberOf _.templateSettings
     * @type {RegExp}
     */
    escape: reEscape,

    /**
     * Used to detect code to be evaluated.
     *
     * @memberOf _.templateSettings
     * @type {RegExp}
     */
    evaluate: reEvaluate,

    /**
     * Used to detect `data` property values to inject.
     *
     * @memberOf _.templateSettings
     * @type {RegExp}
     */
    interpolate: reInterpolate,

    /**
     * Used to reference the data object in the template text.
     *
     * @memberOf _.templateSettings
     * @type {string}
     */
    variable: '',

    /**
     * Used to import variables into the compiled template.
     *
     * @memberOf _.templateSettings
     * @type {Object}
     */
    imports: {
      /**
       * A reference to the `lodash` function.
       *
       * @memberOf _.templateSettings.imports
       * @type {Function}
       */
      _: { escape: escape },
    },
  }

  /** Used to match empty string literals in compiled template source. */
  var reEmptyStringLeading = /\b__p \+= '';/g,
    reEmptyStringMiddle = /\b(__p \+=) '' \+/g,
    reEmptyStringTrailing = /(__e\(.*?\)|\b__t\)) \+\n'';/g

  /**
   * Used to match
   * [ES template delimiters](http://ecma-international.org/ecma-262/7.0/#sec-template-literal-lexical-components).
   */
  var reEsTemplate = /\$\{([^\\}]*(?:\\.[^\\}]*)*)\}/g

  /** Used to ensure capturing order of template delimiters. */
  var reNoMatch = /($^)/

  /** Used to match unescaped characters in compiled string literals. */
  var reUnescapedString = /['\n\r\u2028\u2029\\]/g

  /** Used for built-in method references. */
  var objectProto$r = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$o = objectProto$r.hasOwnProperty

  /**
   * Creates a compiled template function that can interpolate data properties
   * in "interpolate" delimiters, HTML-escape interpolated data properties in
   * "escape" delimiters, and execute JavaScript in "evaluate" delimiters. Data
   * properties may be accessed as free variables in the template. If a setting
   * object is given, it takes precedence over `_.templateSettings` values.
   *
   * **Note:** In the development build `_.template` utilizes
   * [sourceURLs](http://www.html5rocks.com/en/tutorials/developertools/sourcemaps/#toc-sourceurl)
   * for easier debugging.
   *
   * For more information on precompiling templates see
   * [lodash's custom builds documentation](https://lodash.com/custom-builds).
   *
   * For more information on Chrome extension sandboxes see
   * [Chrome's extensions documentation](https://developer.chrome.com/extensions/sandboxingEval).
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category String
   * @param {string} [string=''] The template string.
   * @param {Object} [options={}] The options object.
   * @param {RegExp} [options.escape=_.templateSettings.escape]
   *  The HTML "escape" delimiter.
   * @param {RegExp} [options.evaluate=_.templateSettings.evaluate]
   *  The "evaluate" delimiter.
   * @param {Object} [options.imports=_.templateSettings.imports]
   *  An object to import into the template as free variables.
   * @param {RegExp} [options.interpolate=_.templateSettings.interpolate]
   *  The "interpolate" delimiter.
   * @param {string} [options.sourceURL='templateSources[n]']
   *  The sourceURL of the compiled template.
   * @param {string} [options.variable='obj']
   *  The data object variable name.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {Function} Returns the compiled template function.
   * @example
   *
   * // Use the "interpolate" delimiter to create a compiled template.
   * var compiled = _.template('hello <%= user %>!');
   * compiled({ 'user': 'fred' });
   * // => 'hello fred!'
   *
   * // Use the HTML "escape" delimiter to escape data property values.
   * var compiled = _.template('<b><%- value %></b>');
   * compiled({ 'value': '<script>' });
   * // => '<b>&lt;script&gt;</b>'
   *
   * // Use the "evaluate" delimiter to execute JavaScript and generate HTML.
   * var compiled = _.template('<% _.forEach(users, function(user) { %><li><%- user %></li><% }); %>');
   * compiled({ 'users': ['fred', 'barney'] });
   * // => '<li>fred</li><li>barney</li>'
   *
   * // Use the internal `print` function in "evaluate" delimiters.
   * var compiled = _.template('<% print("hello " + user); %>!');
   * compiled({ 'user': 'barney' });
   * // => 'hello barney!'
   *
   * // Use the ES template literal delimiter as an "interpolate" delimiter.
   * // Disable support by replacing the "interpolate" delimiter.
   * var compiled = _.template('hello ${ user }!');
   * compiled({ 'user': 'pebbles' });
   * // => 'hello pebbles!'
   *
   * // Use backslashes to treat delimiters as plain text.
   * var compiled = _.template('<%= "\\<%- value %\\>" %>');
   * compiled({ 'value': 'ignored' });
   * // => '<%- value %>'
   *
   * // Use the `imports` option to import `jQuery` as `jq`.
   * var text = '<% jq.each(users, function(user) { %><li><%- user %></li><% }); %>';
   * var compiled = _.template(text, { 'imports': { 'jq': jQuery } });
   * compiled({ 'users': ['fred', 'barney'] });
   * // => '<li>fred</li><li>barney</li>'
   *
   * // Use the `sourceURL` option to specify a custom sourceURL for the template.
   * var compiled = _.template('hello <%= user %>!', { 'sourceURL': '/basic/greeting.jst' });
   * compiled(data);
   * // => Find the source of "greeting.jst" under the Sources tab or Resources panel of the web inspector.
   *
   * // Use the `variable` option to ensure a with-statement isn't used in the compiled template.
   * var compiled = _.template('hi <%= data.user %>!', { 'variable': 'data' });
   * compiled.source;
   * // => function(data) {
   * //   var __t, __p = '';
   * //   __p += 'hi ' + ((__t = ( data.user )) == null ? '' : __t) + '!';
   * //   return __p;
   * // }
   *
   * // Use custom template delimiters.
   * _.templateSettings.interpolate = /{{([\s\S]+?)}}/g;
   * var compiled = _.template('hello {{ user }}!');
   * compiled({ 'user': 'mustache' });
   * // => 'hello mustache!'
   *
   * // Use the `source` property to inline compiled templates for meaningful
   * // line numbers in error messages and stack traces.
   * fs.writeFileSync(path.join(process.cwd(), 'jst.js'), '\
   *   var JST = {\
   *     "main": ' + _.template(mainText).source + '\
   *   };\
   * ');
   */
  function template(string, options, guard) {
    // Based on John Resig's `tmpl` implementation
    // (http://ejohn.org/blog/javascript-micro-templating/)
    // and Laura Doktorova's doT.js (https://github.com/olado/doT).
    var settings =
      templateSettings.imports._.templateSettings || templateSettings

    if (guard && isIterateeCall(string, options, guard)) {
      options = undefined
    }
    string = toString(string)
    options = assignInWith({}, options, settings, customDefaultsAssignIn)

    var imports = assignInWith(
        {},
        options.imports,
        settings.imports,
        customDefaultsAssignIn
      ),
      importsKeys = keys(imports),
      importsValues = baseValues(imports, importsKeys)

    var isEscaping,
      isEvaluating,
      index = 0,
      interpolate = options.interpolate || reNoMatch,
      source = "__p += '"

    // Compile the regexp to match each delimiter.
    var reDelimiters = RegExp(
      (options.escape || reNoMatch).source +
        '|' +
        interpolate.source +
        '|' +
        (interpolate === reInterpolate ? reEsTemplate : reNoMatch).source +
        '|' +
        (options.evaluate || reNoMatch).source +
        '|$',
      'g'
    )

    // Use a sourceURL for easier debugging.
    // The sourceURL gets injected into the source that's eval-ed, so be careful
    // with lookup (in case of e.g. prototype pollution), and strip newlines if any.
    // A newline wouldn't be a valid sourceURL anyway, and it'd enable code injection.
    var sourceURL = hasOwnProperty$o.call(options, 'sourceURL')
      ? '//# sourceURL=' +
        (options.sourceURL + '').replace(/[\r\n]/g, ' ') +
        '\n'
      : ''

    string.replace(reDelimiters, function(
      match,
      escapeValue,
      interpolateValue,
      esTemplateValue,
      evaluateValue,
      offset
    ) {
      interpolateValue || (interpolateValue = esTemplateValue)

      // Escape characters that can't be included in string literals.
      source += string
        .slice(index, offset)
        .replace(reUnescapedString, escapeStringChar)

      // Replace delimiters with snippets.
      if (escapeValue) {
        isEscaping = true
        source += "' +\n__e(" + escapeValue + ") +\n'"
      }
      if (evaluateValue) {
        isEvaluating = true
        source += "';\n" + evaluateValue + ";\n__p += '"
      }
      if (interpolateValue) {
        source +=
          "' +\n((__t = (" + interpolateValue + ")) == null ? '' : __t) +\n'"
      }
      index = offset + match.length

      // The JS engine embedded in Adobe products needs `match` returned in
      // order to produce the correct `offset` value.
      return match
    })

    source += "';\n"

    // If `variable` is not specified wrap a with-statement around the generated
    // code to add the data object to the top of the scope chain.
    // Like with sourceURL, we take care to not check the option's prototype,
    // as this configuration is a code injection vector.
    var variable =
      hasOwnProperty$o.call(options, 'variable') && options.variable
    if (!variable) {
      source = 'with (obj) {\n' + source + '\n}\n'
    }
    // Cleanup code by stripping empty strings.
    source = (isEvaluating ? source.replace(reEmptyStringLeading, '') : source)
      .replace(reEmptyStringMiddle, '$1')
      .replace(reEmptyStringTrailing, '$1;')

    // Frame code as the function body.
    source =
      'function(' +
      (variable || 'obj') +
      ') {\n' +
      (variable ? '' : 'obj || (obj = {});\n') +
      "var __t, __p = ''" +
      (isEscaping ? ', __e = _.escape' : '') +
      (isEvaluating
        ? ', __j = Array.prototype.join;\n' +
          "function print() { __p += __j.call(arguments, '') }\n"
        : ';\n') +
      source +
      'return __p\n}'

    var result = attempt(function() {
      return Function(importsKeys, sourceURL + 'return ' + source).apply(
        undefined,
        importsValues
      )
    })

    // Provide the compiled function's source by its `toString` method or
    // the `source` property as a convenience for inlining compiled templates.
    result.source = source
    if (isError(result)) {
      throw result
    }
    return result
  }

  /** Error message constants. */
  var FUNC_ERROR_TEXT$b = 'Expected a function'

  /**
   * Creates a throttled function that only invokes `func` at most once per
   * every `wait` milliseconds. The throttled function comes with a `cancel`
   * method to cancel delayed `func` invocations and a `flush` method to
   * immediately invoke them. Provide `options` to indicate whether `func`
   * should be invoked on the leading and/or trailing edge of the `wait`
   * timeout. The `func` is invoked with the last arguments provided to the
   * throttled function. Subsequent calls to the throttled function return the
   * result of the last `func` invocation.
   *
   * **Note:** If `leading` and `trailing` options are `true`, `func` is
   * invoked on the trailing edge of the timeout only if the throttled function
   * is invoked more than once during the `wait` timeout.
   *
   * If `wait` is `0` and `leading` is `false`, `func` invocation is deferred
   * until to the next tick, similar to `setTimeout` with a timeout of `0`.
   *
   * See [David Corbacho's article](https://css-tricks.com/debouncing-throttling-explained-examples/)
   * for details over the differences between `_.throttle` and `_.debounce`.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {Function} func The function to throttle.
   * @param {number} [wait=0] The number of milliseconds to throttle invocations to.
   * @param {Object} [options={}] The options object.
   * @param {boolean} [options.leading=true]
   *  Specify invoking on the leading edge of the timeout.
   * @param {boolean} [options.trailing=true]
   *  Specify invoking on the trailing edge of the timeout.
   * @returns {Function} Returns the new throttled function.
   * @example
   *
   * // Avoid excessively updating the position while scrolling.
   * jQuery(window).on('scroll', _.throttle(updatePosition, 100));
   *
   * // Invoke `renewToken` when the click event is fired, but not more than once every 5 minutes.
   * var throttled = _.throttle(renewToken, 300000, { 'trailing': false });
   * jQuery(element).on('click', throttled);
   *
   * // Cancel the trailing throttled invocation.
   * jQuery(window).on('popstate', throttled.cancel);
   */
  function throttle(func, wait, options) {
    var leading = true,
      trailing = true

    if (typeof func != 'function') {
      throw new TypeError(FUNC_ERROR_TEXT$b)
    }
    if (isObject(options)) {
      leading = 'leading' in options ? !!options.leading : leading
      trailing = 'trailing' in options ? !!options.trailing : trailing
    }
    return debounce(func, wait, {
      leading: leading,
      maxWait: wait,
      trailing: trailing,
    })
  }

  /**
   * This method is like `_.tap` except that it returns the result of `interceptor`.
   * The purpose of this method is to "pass thru" values replacing intermediate
   * results in a method chain sequence.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Seq
   * @param {*} value The value to provide to `interceptor`.
   * @param {Function} interceptor The function to invoke.
   * @returns {*} Returns the result of `interceptor`.
   * @example
   *
   * _('  abc  ')
   *  .chain()
   *  .trim()
   *  .thru(function(value) {
   *    return [value];
   *  })
   *  .value();
   * // => ['abc']
   */
  function thru(value, interceptor) {
    return interceptor(value)
  }

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER$4 = 9007199254740991

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH$5 = 4294967295

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin$b = Math.min

  /**
   * Invokes the iteratee `n` times, returning an array of the results of
   * each invocation. The iteratee is invoked with one argument; (index).
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {number} n The number of times to invoke `iteratee`.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @returns {Array} Returns the array of results.
   * @example
   *
   * _.times(3, String);
   * // => ['0', '1', '2']
   *
   *  _.times(4, _.constant(0));
   * // => [0, 0, 0, 0]
   */
  function times(n, iteratee) {
    n = toInteger(n)
    if (n < 1 || n > MAX_SAFE_INTEGER$4) {
      return []
    }
    var index = MAX_ARRAY_LENGTH$5,
      length = nativeMin$b(n, MAX_ARRAY_LENGTH$5)

    iteratee = castFunction(iteratee)
    n -= MAX_ARRAY_LENGTH$5

    var result = baseTimes(length, iteratee)
    while (++index < n) {
      iteratee(index)
    }
    return result
  }

  /**
   * Enables the wrapper to be iterable.
   *
   * @name Symbol.iterator
   * @memberOf _
   * @since 4.0.0
   * @category Seq
   * @returns {Object} Returns the wrapper object.
   * @example
   *
   * var wrapped = _([1, 2]);
   *
   * wrapped[Symbol.iterator]() === wrapped;
   * // => true
   *
   * Array.from(wrapped);
   * // => [1, 2]
   */
  function wrapperToIterator() {
    return this
  }

  /**
   * The base implementation of `wrapperValue` which returns the result of
   * performing a sequence of actions on the unwrapped `value`, where each
   * successive action is supplied the return value of the previous.
   *
   * @private
   * @param {*} value The unwrapped value.
   * @param {Array} actions Actions to perform to resolve the unwrapped value.
   * @returns {*} Returns the resolved value.
   */
  function baseWrapperValue(value, actions) {
    var result = value
    if (result instanceof LazyWrapper) {
      result = result.value()
    }
    return arrayReduce(
      actions,
      function(result, action) {
        return action.func.apply(
          action.thisArg,
          arrayPush([result], action.args)
        )
      },
      result
    )
  }

  /**
   * Executes the chain sequence to resolve the unwrapped value.
   *
   * @name value
   * @memberOf _
   * @since 0.1.0
   * @alias toJSON, valueOf
   * @category Seq
   * @returns {*} Returns the resolved unwrapped value.
   * @example
   *
   * _([1, 2, 3]).value();
   * // => [1, 2, 3]
   */
  function wrapperValue() {
    return baseWrapperValue(this.__wrapped__, this.__actions__)
  }

  /**
   * Converts `string`, as a whole, to lower case just like
   * [String#toLowerCase](https://mdn.io/toLowerCase).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the lower cased string.
   * @example
   *
   * _.toLower('--Foo-Bar--');
   * // => '--foo-bar--'
   *
   * _.toLower('fooBar');
   * // => 'foobar'
   *
   * _.toLower('__FOO_BAR__');
   * // => '__foo_bar__'
   */
  function toLower(value) {
    return toString(value).toLowerCase()
  }

  /**
   * Converts `value` to a property path array.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Util
   * @param {*} value The value to convert.
   * @returns {Array} Returns the new property path array.
   * @example
   *
   * _.toPath('a.b.c');
   * // => ['a', 'b', 'c']
   *
   * _.toPath('a[0].b.c');
   * // => ['a', '0', 'b', 'c']
   */
  function toPath(value) {
    if (isArray(value)) {
      return arrayMap(value, toKey)
    }
    return isSymbol(value) ? [value] : copyArray(stringToPath(toString(value)))
  }

  /** Used as references for various `Number` constants. */
  var MAX_SAFE_INTEGER$5 = 9007199254740991

  /**
   * Converts `value` to a safe integer. A safe integer can be compared and
   * represented correctly.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Lang
   * @param {*} value The value to convert.
   * @returns {number} Returns the converted integer.
   * @example
   *
   * _.toSafeInteger(3.2);
   * // => 3
   *
   * _.toSafeInteger(Number.MIN_VALUE);
   * // => 0
   *
   * _.toSafeInteger(Infinity);
   * // => 9007199254740991
   *
   * _.toSafeInteger('3.2');
   * // => 3
   */
  function toSafeInteger(value) {
    return value
      ? baseClamp(toInteger(value), -MAX_SAFE_INTEGER$5, MAX_SAFE_INTEGER$5)
      : value === 0
      ? value
      : 0
  }

  /**
   * Converts `string`, as a whole, to upper case just like
   * [String#toUpperCase](https://mdn.io/toUpperCase).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the upper cased string.
   * @example
   *
   * _.toUpper('--foo-bar--');
   * // => '--FOO-BAR--'
   *
   * _.toUpper('fooBar');
   * // => 'FOOBAR'
   *
   * _.toUpper('__foo_bar__');
   * // => '__FOO_BAR__'
   */
  function toUpper(value) {
    return toString(value).toUpperCase()
  }

  /**
   * An alternative to `_.reduce`; this method transforms `object` to a new
   * `accumulator` object which is the result of running each of its own
   * enumerable string keyed properties thru `iteratee`, with each invocation
   * potentially mutating the `accumulator` object. If `accumulator` is not
   * provided, a new object with the same `[[Prototype]]` will be used. The
   * iteratee is invoked with four arguments: (accumulator, value, key, object).
   * Iteratee functions may exit iteration early by explicitly returning `false`.
   *
   * @static
   * @memberOf _
   * @since 1.3.0
   * @category Object
   * @param {Object} object The object to iterate over.
   * @param {Function} [iteratee=_.identity] The function invoked per iteration.
   * @param {*} [accumulator] The custom accumulator value.
   * @returns {*} Returns the accumulated value.
   * @example
   *
   * _.transform([2, 3, 4], function(result, n) {
   *   result.push(n *= n);
   *   return n % 2 == 0;
   * }, []);
   * // => [4, 9]
   *
   * _.transform({ 'a': 1, 'b': 2, 'c': 1 }, function(result, value, key) {
   *   (result[value] || (result[value] = [])).push(key);
   * }, {});
   * // => { '1': ['a', 'c'], '2': ['b'] }
   */
  function transform(object, iteratee, accumulator) {
    var isArr = isArray(object),
      isArrLike = isArr || isBuffer(object) || isTypedArray(object)

    iteratee = baseIteratee(iteratee)
    if (accumulator == null) {
      var Ctor = object && object.constructor
      if (isArrLike) {
        accumulator = isArr ? new Ctor() : []
      } else if (isObject(object)) {
        accumulator = isFunction(Ctor) ? baseCreate(getPrototype(object)) : {}
      } else {
        accumulator = {}
      }
    }
    ;(isArrLike
      ? arrayEach
      : baseForOwn)(object, function(value, index, object) {
      return iteratee(accumulator, value, index, object)
    })
    return accumulator
  }

  /**
   * Used by `_.trim` and `_.trimEnd` to get the index of the last string symbol
   * that is not found in the character symbols.
   *
   * @private
   * @param {Array} strSymbols The string symbols to inspect.
   * @param {Array} chrSymbols The character symbols to find.
   * @returns {number} Returns the index of the last unmatched string symbol.
   */
  function charsEndIndex(strSymbols, chrSymbols) {
    var index = strSymbols.length

    while (index-- && baseIndexOf(chrSymbols, strSymbols[index], 0) > -1) {}
    return index
  }

  /**
   * Used by `_.trim` and `_.trimStart` to get the index of the first string symbol
   * that is not found in the character symbols.
   *
   * @private
   * @param {Array} strSymbols The string symbols to inspect.
   * @param {Array} chrSymbols The character symbols to find.
   * @returns {number} Returns the index of the first unmatched string symbol.
   */
  function charsStartIndex(strSymbols, chrSymbols) {
    var index = -1,
      length = strSymbols.length

    while (
      ++index < length &&
      baseIndexOf(chrSymbols, strSymbols[index], 0) > -1
    ) {}
    return index
  }

  /** Used to match leading and trailing whitespace. */
  var reTrim$1 = /^\s+|\s+$/g

  /**
   * Removes leading and trailing whitespace or specified characters from `string`.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category String
   * @param {string} [string=''] The string to trim.
   * @param {string} [chars=whitespace] The characters to trim.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {string} Returns the trimmed string.
   * @example
   *
   * _.trim('  abc  ');
   * // => 'abc'
   *
   * _.trim('-_-abc-_-', '_-');
   * // => 'abc'
   *
   * _.map(['  foo  ', '  bar  '], _.trim);
   * // => ['foo', 'bar']
   */
  function trim(string, chars, guard) {
    string = toString(string)
    if (string && (guard || chars === undefined)) {
      return string.replace(reTrim$1, '')
    }
    if (!string || !(chars = baseToString(chars))) {
      return string
    }
    var strSymbols = stringToArray(string),
      chrSymbols = stringToArray(chars),
      start = charsStartIndex(strSymbols, chrSymbols),
      end = charsEndIndex(strSymbols, chrSymbols) + 1

    return castSlice(strSymbols, start, end).join('')
  }

  /** Used to match leading and trailing whitespace. */
  var reTrimEnd = /\s+$/

  /**
   * Removes trailing whitespace or specified characters from `string`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to trim.
   * @param {string} [chars=whitespace] The characters to trim.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {string} Returns the trimmed string.
   * @example
   *
   * _.trimEnd('  abc  ');
   * // => '  abc'
   *
   * _.trimEnd('-_-abc-_-', '_-');
   * // => '-_-abc'
   */
  function trimEnd(string, chars, guard) {
    string = toString(string)
    if (string && (guard || chars === undefined)) {
      return string.replace(reTrimEnd, '')
    }
    if (!string || !(chars = baseToString(chars))) {
      return string
    }
    var strSymbols = stringToArray(string),
      end = charsEndIndex(strSymbols, stringToArray(chars)) + 1

    return castSlice(strSymbols, 0, end).join('')
  }

  /** Used to match leading and trailing whitespace. */
  var reTrimStart$1 = /^\s+/

  /**
   * Removes leading whitespace or specified characters from `string`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to trim.
   * @param {string} [chars=whitespace] The characters to trim.
   * @param- {Object} [guard] Enables use as an iteratee for methods like `_.map`.
   * @returns {string} Returns the trimmed string.
   * @example
   *
   * _.trimStart('  abc  ');
   * // => 'abc  '
   *
   * _.trimStart('-_-abc-_-', '_-');
   * // => 'abc-_-'
   */
  function trimStart(string, chars, guard) {
    string = toString(string)
    if (string && (guard || chars === undefined)) {
      return string.replace(reTrimStart$1, '')
    }
    if (!string || !(chars = baseToString(chars))) {
      return string
    }
    var strSymbols = stringToArray(string),
      start = charsStartIndex(strSymbols, stringToArray(chars))

    return castSlice(strSymbols, start).join('')
  }

  /** Used as default options for `_.truncate`. */
  var DEFAULT_TRUNC_LENGTH = 30,
    DEFAULT_TRUNC_OMISSION = '...'

  /** Used to match `RegExp` flags from their coerced string values. */
  var reFlags$1 = /\w*$/

  /**
   * Truncates `string` if it's longer than the given maximum string length.
   * The last characters of the truncated string are replaced with the omission
   * string which defaults to "...".
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to truncate.
   * @param {Object} [options={}] The options object.
   * @param {number} [options.length=30] The maximum string length.
   * @param {string} [options.omission='...'] The string to indicate text is omitted.
   * @param {RegExp|string} [options.separator] The separator pattern to truncate to.
   * @returns {string} Returns the truncated string.
   * @example
   *
   * _.truncate('hi-diddly-ho there, neighborino');
   * // => 'hi-diddly-ho there, neighbo...'
   *
   * _.truncate('hi-diddly-ho there, neighborino', {
   *   'length': 24,
   *   'separator': ' '
   * });
   * // => 'hi-diddly-ho there,...'
   *
   * _.truncate('hi-diddly-ho there, neighborino', {
   *   'length': 24,
   *   'separator': /,? +/
   * });
   * // => 'hi-diddly-ho there...'
   *
   * _.truncate('hi-diddly-ho there, neighborino', {
   *   'omission': ' [...]'
   * });
   * // => 'hi-diddly-ho there, neig [...]'
   */
  function truncate(string, options) {
    var length = DEFAULT_TRUNC_LENGTH,
      omission = DEFAULT_TRUNC_OMISSION

    if (isObject(options)) {
      var separator = 'separator' in options ? options.separator : separator
      length = 'length' in options ? toInteger(options.length) : length
      omission =
        'omission' in options ? baseToString(options.omission) : omission
    }
    string = toString(string)

    var strLength = string.length
    if (hasUnicode(string)) {
      var strSymbols = stringToArray(string)
      strLength = strSymbols.length
    }
    if (length >= strLength) {
      return string
    }
    var end = length - stringSize(omission)
    if (end < 1) {
      return omission
    }
    var result = strSymbols
      ? castSlice(strSymbols, 0, end).join('')
      : string.slice(0, end)

    if (separator === undefined) {
      return result + omission
    }
    if (strSymbols) {
      end += result.length - end
    }
    if (isRegExp(separator)) {
      if (string.slice(end).search(separator)) {
        var match,
          substring = result

        if (!separator.global) {
          separator = RegExp(
            separator.source,
            toString(reFlags$1.exec(separator)) + 'g'
          )
        }
        separator.lastIndex = 0
        while ((match = separator.exec(substring))) {
          var newEnd = match.index
        }
        result = result.slice(0, newEnd === undefined ? end : newEnd)
      }
    } else if (string.indexOf(baseToString(separator), end) != end) {
      var index = result.lastIndexOf(separator)
      if (index > -1) {
        result = result.slice(0, index)
      }
    }
    return result + omission
  }

  /**
   * Creates a function that accepts up to one argument, ignoring any
   * additional arguments.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Function
   * @param {Function} func The function to cap arguments for.
   * @returns {Function} Returns the new capped function.
   * @example
   *
   * _.map(['6', '8', '10'], _.unary(parseInt));
   * // => [6, 8, 10]
   */
  function unary(func) {
    return ary(func, 1)
  }

  /** Used to map HTML entities to characters. */
  var htmlUnescapes = {
    '&amp;': '&',
    '&lt;': '<',
    '&gt;': '>',
    '&quot;': '"',
    '&#39;': "'",
  }

  /**
   * Used by `_.unescape` to convert HTML entities to characters.
   *
   * @private
   * @param {string} chr The matched character to unescape.
   * @returns {string} Returns the unescaped character.
   */
  var unescapeHtmlChar = basePropertyOf(htmlUnescapes)

  /** Used to match HTML entities and HTML characters. */
  var reEscapedHtml = /&(?:amp|lt|gt|quot|#39);/g,
    reHasEscapedHtml = RegExp(reEscapedHtml.source)

  /**
   * The inverse of `_.escape`; this method converts the HTML entities
   * `&amp;`, `&lt;`, `&gt;`, `&quot;`, and `&#39;` in `string` to
   * their corresponding characters.
   *
   * **Note:** No other HTML entities are unescaped. To unescape additional
   * HTML entities use a third-party library like [_he_](https://mths.be/he).
   *
   * @static
   * @memberOf _
   * @since 0.6.0
   * @category String
   * @param {string} [string=''] The string to unescape.
   * @returns {string} Returns the unescaped string.
   * @example
   *
   * _.unescape('fred, barney, &amp; pebbles');
   * // => 'fred, barney, & pebbles'
   */
  function unescape(string) {
    string = toString(string)
    return string && reHasEscapedHtml.test(string)
      ? string.replace(reEscapedHtml, unescapeHtmlChar)
      : string
  }

  /** Used as references for various `Number` constants. */
  var INFINITY$5 = 1 / 0

  /**
   * Creates a set object of `values`.
   *
   * @private
   * @param {Array} values The values to add to the set.
   * @returns {Object} Returns the new set.
   */
  var createSet = !(Set && 1 / setToArray(new Set([, -0]))[1] == INFINITY$5)
    ? noop$1
    : function(values) {
        return new Set(values)
      }

  /** Used as the size to enable large array optimizations. */
  var LARGE_ARRAY_SIZE$2 = 200

  /**
   * The base implementation of `_.uniqBy` without support for iteratee shorthands.
   *
   * @private
   * @param {Array} array The array to inspect.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new duplicate free array.
   */
  function baseUniq(array, iteratee, comparator) {
    var index = -1,
      includes = arrayIncludes,
      length = array.length,
      isCommon = true,
      result = [],
      seen = result

    if (comparator) {
      isCommon = false
      includes = arrayIncludesWith
    } else if (length >= LARGE_ARRAY_SIZE$2) {
      var set = iteratee ? null : createSet(array)
      if (set) {
        return setToArray(set)
      }
      isCommon = false
      includes = cacheHas
      seen = new SetCache()
    } else {
      seen = iteratee ? [] : result
    }
    outer: while (++index < length) {
      var value = array[index],
        computed = iteratee ? iteratee(value) : value

      value = comparator || value !== 0 ? value : 0
      if (isCommon && computed === computed) {
        var seenIndex = seen.length
        while (seenIndex--) {
          if (seen[seenIndex] === computed) {
            continue outer
          }
        }
        if (iteratee) {
          seen.push(computed)
        }
        result.push(value)
      } else if (!includes(seen, computed, comparator)) {
        if (seen !== result) {
          seen.push(computed)
        }
        result.push(value)
      }
    }
    return result
  }

  /**
   * Creates an array of unique values, in order, from all given arrays using
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @returns {Array} Returns the new array of combined values.
   * @example
   *
   * _.union([2], [1, 2]);
   * // => [2, 1]
   */
  var union = baseRest(function(arrays) {
    return baseUniq(baseFlatten(arrays, 1, isArrayLikeObject, true))
  })

  /**
   * This method is like `_.union` except that it accepts `iteratee` which is
   * invoked for each element of each `arrays` to generate the criterion by
   * which uniqueness is computed. Result values are chosen from the first
   * array in which the value occurs. The iteratee is invoked with one argument:
   * (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Array} Returns the new array of combined values.
   * @example
   *
   * _.unionBy([2.1], [1.2, 2.3], Math.floor);
   * // => [2.1, 1.2]
   *
   * // The `_.property` iteratee shorthand.
   * _.unionBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
   * // => [{ 'x': 1 }, { 'x': 2 }]
   */
  var unionBy = baseRest(function(arrays) {
    var iteratee = last(arrays)
    if (isArrayLikeObject(iteratee)) {
      iteratee = undefined
    }
    return baseUniq(
      baseFlatten(arrays, 1, isArrayLikeObject, true),
      baseIteratee(iteratee)
    )
  })

  /**
   * This method is like `_.union` except that it accepts `comparator` which
   * is invoked to compare elements of `arrays`. Result values are chosen from
   * the first array in which the value occurs. The comparator is invoked
   * with two arguments: (arrVal, othVal).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of combined values.
   * @example
   *
   * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
   * var others = [{ 'x': 1, 'y': 1 }, { 'x': 1, 'y': 2 }];
   *
   * _.unionWith(objects, others, _.isEqual);
   * // => [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }, { 'x': 1, 'y': 1 }]
   */
  var unionWith = baseRest(function(arrays) {
    var comparator = last(arrays)
    comparator = typeof comparator == 'function' ? comparator : undefined
    return baseUniq(
      baseFlatten(arrays, 1, isArrayLikeObject, true),
      undefined,
      comparator
    )
  })

  /**
   * Creates a duplicate-free version of an array, using
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons, in which only the first occurrence of each element
   * is kept. The order of result values is determined by the order they occur
   * in the array.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @returns {Array} Returns the new duplicate free array.
   * @example
   *
   * _.uniq([2, 1, 2]);
   * // => [2, 1]
   */
  function uniq(array) {
    return array && array.length ? baseUniq(array) : []
  }

  /**
   * This method is like `_.uniq` except that it accepts `iteratee` which is
   * invoked for each element in `array` to generate the criterion by which
   * uniqueness is computed. The order of result values is determined by the
   * order they occur in the array. The iteratee is invoked with one argument:
   * (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Array} Returns the new duplicate free array.
   * @example
   *
   * _.uniqBy([2.1, 1.2, 2.3], Math.floor);
   * // => [2.1, 1.2]
   *
   * // The `_.property` iteratee shorthand.
   * _.uniqBy([{ 'x': 1 }, { 'x': 2 }, { 'x': 1 }], 'x');
   * // => [{ 'x': 1 }, { 'x': 2 }]
   */
  function uniqBy(array, iteratee) {
    return array && array.length ? baseUniq(array, baseIteratee(iteratee)) : []
  }

  /**
   * This method is like `_.uniq` except that it accepts `comparator` which
   * is invoked to compare elements of `array`. The order of result values is
   * determined by the order they occur in the array.The comparator is invoked
   * with two arguments: (arrVal, othVal).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new duplicate free array.
   * @example
   *
   * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }, { 'x': 1, 'y': 2 }];
   *
   * _.uniqWith(objects, _.isEqual);
   * // => [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }]
   */
  function uniqWith(array, comparator) {
    comparator = typeof comparator == 'function' ? comparator : undefined
    return array && array.length ? baseUniq(array, undefined, comparator) : []
  }

  /** Used to generate unique IDs. */
  var idCounter = 0

  /**
   * Generates a unique ID. If `prefix` is given, the ID is appended to it.
   *
   * @static
   * @since 0.1.0
   * @memberOf _
   * @category Util
   * @param {string} [prefix=''] The value to prefix the ID with.
   * @returns {string} Returns the unique ID.
   * @example
   *
   * _.uniqueId('contact_');
   * // => 'contact_104'
   *
   * _.uniqueId();
   * // => '105'
   */
  function uniqueId(prefix) {
    var id = ++idCounter
    return toString(prefix) + id
  }

  /**
   * Removes the property at `path` of `object`.
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Object
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to unset.
   * @returns {boolean} Returns `true` if the property is deleted, else `false`.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 7 } }] };
   * _.unset(object, 'a[0].b.c');
   * // => true
   *
   * console.log(object);
   * // => { 'a': [{ 'b': {} }] };
   *
   * _.unset(object, ['a', '0', 'b', 'c']);
   * // => true
   *
   * console.log(object);
   * // => { 'a': [{ 'b': {} }] };
   */
  function unset(object, path) {
    return object == null ? true : baseUnset(object, path)
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$e = Math.max

  /**
   * This method is like `_.zip` except that it accepts an array of grouped
   * elements and creates an array regrouping the elements to their pre-zip
   * configuration.
   *
   * @static
   * @memberOf _
   * @since 1.2.0
   * @category Array
   * @param {Array} array The array of grouped elements to process.
   * @returns {Array} Returns the new array of regrouped elements.
   * @example
   *
   * var zipped = _.zip(['a', 'b'], [1, 2], [true, false]);
   * // => [['a', 1, true], ['b', 2, false]]
   *
   * _.unzip(zipped);
   * // => [['a', 'b'], [1, 2], [true, false]]
   */
  function unzip(array) {
    if (!(array && array.length)) {
      return []
    }
    var length = 0
    array = arrayFilter(array, function(group) {
      if (isArrayLikeObject(group)) {
        length = nativeMax$e(group.length, length)
        return true
      }
    })
    return baseTimes(length, function(index) {
      return arrayMap(array, baseProperty(index))
    })
  }

  /**
   * This method is like `_.unzip` except that it accepts `iteratee` to specify
   * how regrouped values should be combined. The iteratee is invoked with the
   * elements of each group: (...group).
   *
   * @static
   * @memberOf _
   * @since 3.8.0
   * @category Array
   * @param {Array} array The array of grouped elements to process.
   * @param {Function} [iteratee=_.identity] The function to combine
   *  regrouped values.
   * @returns {Array} Returns the new array of regrouped elements.
   * @example
   *
   * var zipped = _.zip([1, 2], [10, 20], [100, 200]);
   * // => [[1, 10, 100], [2, 20, 200]]
   *
   * _.unzipWith(zipped, _.add);
   * // => [3, 30, 300]
   */
  function unzipWith(array, iteratee) {
    if (!(array && array.length)) {
      return []
    }
    var result = unzip(array)
    if (iteratee == null) {
      return result
    }
    return arrayMap(result, function(group) {
      return apply(iteratee, undefined, group)
    })
  }

  /**
   * The base implementation of `_.update`.
   *
   * @private
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to update.
   * @param {Function} updater The function to produce the updated value.
   * @param {Function} [customizer] The function to customize path creation.
   * @returns {Object} Returns `object`.
   */
  function baseUpdate(object, path, updater, customizer) {
    return baseSet(object, path, updater(baseGet(object, path)), customizer)
  }

  /**
   * This method is like `_.set` except that accepts `updater` to produce the
   * value to set. Use `_.updateWith` to customize `path` creation. The `updater`
   * is invoked with one argument: (value).
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.6.0
   * @category Object
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to set.
   * @param {Function} updater The function to produce the updated value.
   * @returns {Object} Returns `object`.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 3 } }] };
   *
   * _.update(object, 'a[0].b.c', function(n) { return n * n; });
   * console.log(object.a[0].b.c);
   * // => 9
   *
   * _.update(object, 'x[0].y.z', function(n) { return n ? n + 1 : 0; });
   * console.log(object.x[0].y.z);
   * // => 0
   */
  function update(object, path, updater) {
    return object == null
      ? object
      : baseUpdate(object, path, castFunction(updater))
  }

  /**
   * This method is like `_.update` except that it accepts `customizer` which is
   * invoked to produce the objects of `path`.  If `customizer` returns `undefined`
   * path creation is handled by the method instead. The `customizer` is invoked
   * with three arguments: (nsValue, key, nsObject).
   *
   * **Note:** This method mutates `object`.
   *
   * @static
   * @memberOf _
   * @since 4.6.0
   * @category Object
   * @param {Object} object The object to modify.
   * @param {Array|string} path The path of the property to set.
   * @param {Function} updater The function to produce the updated value.
   * @param {Function} [customizer] The function to customize assigned values.
   * @returns {Object} Returns `object`.
   * @example
   *
   * var object = {};
   *
   * _.updateWith(object, '[0][1]', _.constant('a'), Object);
   * // => { '0': { '1': 'a' } }
   */
  function updateWith(object, path, updater, customizer) {
    customizer = typeof customizer == 'function' ? customizer : undefined
    return object == null
      ? object
      : baseUpdate(object, path, castFunction(updater), customizer)
  }

  /**
   * Converts `string`, as space separated words, to upper case.
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category String
   * @param {string} [string=''] The string to convert.
   * @returns {string} Returns the upper cased string.
   * @example
   *
   * _.upperCase('--foo-bar');
   * // => 'FOO BAR'
   *
   * _.upperCase('fooBar');
   * // => 'FOO BAR'
   *
   * _.upperCase('__foo_bar__');
   * // => 'FOO BAR'
   */
  var upperCase = createCompounder(function(result, word, index) {
    return result + (index ? ' ' : '') + word.toUpperCase()
  })

  /**
   * Creates an array of the own and inherited enumerable string keyed property
   * values of `object`.
   *
   * **Note:** Non-object values are coerced to objects.
   *
   * @static
   * @memberOf _
   * @since 3.0.0
   * @category Object
   * @param {Object} object The object to query.
   * @returns {Array} Returns the array of property values.
   * @example
   *
   * function Foo() {
   *   this.a = 1;
   *   this.b = 2;
   * }
   *
   * Foo.prototype.c = 3;
   *
   * _.valuesIn(new Foo);
   * // => [1, 2, 3] (iteration order is not guaranteed)
   */
  function valuesIn(object) {
    return object == null ? [] : baseValues(object, keysIn$1(object))
  }

  /**
   * Creates an array excluding all given values using
   * [`SameValueZero`](http://ecma-international.org/ecma-262/7.0/#sec-samevaluezero)
   * for equality comparisons.
   *
   * **Note:** Unlike `_.pull`, this method returns a new array.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {Array} array The array to inspect.
   * @param {...*} [values] The values to exclude.
   * @returns {Array} Returns the new array of filtered values.
   * @see _.difference, _.xor
   * @example
   *
   * _.without([2, 1, 2, 3], 1, 2);
   * // => [3]
   */
  var without = baseRest(function(array, values) {
    return isArrayLikeObject(array) ? baseDifference(array, values) : []
  })

  /**
   * Creates a function that provides `value` to `wrapper` as its first
   * argument. Any additional arguments provided to the function are appended
   * to those provided to the `wrapper`. The wrapper is invoked with the `this`
   * binding of the created function.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Function
   * @param {*} value The value to wrap.
   * @param {Function} [wrapper=identity] The wrapper function.
   * @returns {Function} Returns the new function.
   * @example
   *
   * var p = _.wrap(_.escape, function(func, text) {
   *   return '<p>' + func(text) + '</p>';
   * });
   *
   * p('fred, barney, & pebbles');
   * // => '<p>fred, barney, &amp; pebbles</p>'
   */
  function wrap(value, wrapper) {
    return partial(castFunction(wrapper), value)
  }

  /**
   * This method is the wrapper version of `_.at`.
   *
   * @name at
   * @memberOf _
   * @since 1.0.0
   * @category Seq
   * @param {...(string|string[])} [paths] The property paths to pick.
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * var object = { 'a': [{ 'b': { 'c': 3 } }, 4] };
   *
   * _(object).at(['a[0].b.c', 'a[1]']).value();
   * // => [3, 4]
   */
  var wrapperAt = flatRest(function(paths) {
    var length = paths.length,
      start = length ? paths[0] : 0,
      value = this.__wrapped__,
      interceptor = function(object) {
        return baseAt(object, paths)
      }

    if (
      length > 1 ||
      this.__actions__.length ||
      !(value instanceof LazyWrapper) ||
      !isIndex(start)
    ) {
      return this.thru(interceptor)
    }
    value = value.slice(start, +start + (length ? 1 : 0))
    value.__actions__.push({
      func: thru,
      args: [interceptor],
      thisArg: undefined,
    })
    return new LodashWrapper(value, this.__chain__).thru(function(array) {
      if (length && !array.length) {
        array.push(undefined)
      }
      return array
    })
  })

  /**
   * Creates a `lodash` wrapper instance with explicit method chain sequences enabled.
   *
   * @name chain
   * @memberOf _
   * @since 0.1.0
   * @category Seq
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * var users = [
   *   { 'user': 'barney', 'age': 36 },
   *   { 'user': 'fred',   'age': 40 }
   * ];
   *
   * // A sequence without explicit chaining.
   * _(users).head();
   * // => { 'user': 'barney', 'age': 36 }
   *
   * // A sequence with explicit chaining.
   * _(users)
   *   .chain()
   *   .head()
   *   .pick('user')
   *   .value();
   * // => { 'user': 'barney' }
   */
  function wrapperChain() {
    return chain(this)
  }

  /**
   * This method is the wrapper version of `_.reverse`.
   *
   * **Note:** This method mutates the wrapped array.
   *
   * @name reverse
   * @memberOf _
   * @since 0.1.0
   * @category Seq
   * @returns {Object} Returns the new `lodash` wrapper instance.
   * @example
   *
   * var array = [1, 2, 3];
   *
   * _(array).reverse().value()
   * // => [3, 2, 1]
   *
   * console.log(array);
   * // => [3, 2, 1]
   */
  function wrapperReverse() {
    var value = this.__wrapped__
    if (value instanceof LazyWrapper) {
      var wrapped = value
      if (this.__actions__.length) {
        wrapped = new LazyWrapper(this)
      }
      wrapped = wrapped.reverse()
      wrapped.__actions__.push({
        func: thru,
        args: [reverse],
        thisArg: undefined,
      })
      return new LodashWrapper(wrapped, this.__chain__)
    }
    return this.thru(reverse)
  }

  /**
   * The base implementation of methods like `_.xor`, without support for
   * iteratee shorthands, that accepts an array of arrays to inspect.
   *
   * @private
   * @param {Array} arrays The arrays to inspect.
   * @param {Function} [iteratee] The iteratee invoked per element.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of values.
   */
  function baseXor(arrays, iteratee, comparator) {
    var length = arrays.length
    if (length < 2) {
      return length ? baseUniq(arrays[0]) : []
    }
    var index = -1,
      result = Array(length)

    while (++index < length) {
      var array = arrays[index],
        othIndex = -1

      while (++othIndex < length) {
        if (othIndex != index) {
          result[index] = baseDifference(
            result[index] || array,
            arrays[othIndex],
            iteratee,
            comparator
          )
        }
      }
    }
    return baseUniq(baseFlatten(result, 1), iteratee, comparator)
  }

  /**
   * Creates an array of unique values that is the
   * [symmetric difference](https://en.wikipedia.org/wiki/Symmetric_difference)
   * of the given arrays. The order of result values is determined by the order
   * they occur in the arrays.
   *
   * @static
   * @memberOf _
   * @since 2.4.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @returns {Array} Returns the new array of filtered values.
   * @see _.difference, _.without
   * @example
   *
   * _.xor([2, 1], [2, 3]);
   * // => [1, 3]
   */
  var xor = baseRest(function(arrays) {
    return baseXor(arrayFilter(arrays, isArrayLikeObject))
  })

  /**
   * This method is like `_.xor` except that it accepts `iteratee` which is
   * invoked for each element of each `arrays` to generate the criterion by
   * which by which they're compared. The order of result values is determined
   * by the order they occur in the arrays. The iteratee is invoked with one
   * argument: (value).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @param {Function} [iteratee=_.identity] The iteratee invoked per element.
   * @returns {Array} Returns the new array of filtered values.
   * @example
   *
   * _.xorBy([2.1, 1.2], [2.3, 3.4], Math.floor);
   * // => [1.2, 3.4]
   *
   * // The `_.property` iteratee shorthand.
   * _.xorBy([{ 'x': 1 }], [{ 'x': 2 }, { 'x': 1 }], 'x');
   * // => [{ 'x': 2 }]
   */
  var xorBy = baseRest(function(arrays) {
    var iteratee = last(arrays)
    if (isArrayLikeObject(iteratee)) {
      iteratee = undefined
    }
    return baseXor(
      arrayFilter(arrays, isArrayLikeObject),
      baseIteratee(iteratee)
    )
  })

  /**
   * This method is like `_.xor` except that it accepts `comparator` which is
   * invoked to compare elements of `arrays`. The order of result values is
   * determined by the order they occur in the arrays. The comparator is invoked
   * with two arguments: (arrVal, othVal).
   *
   * @static
   * @memberOf _
   * @since 4.0.0
   * @category Array
   * @param {...Array} [arrays] The arrays to inspect.
   * @param {Function} [comparator] The comparator invoked per element.
   * @returns {Array} Returns the new array of filtered values.
   * @example
   *
   * var objects = [{ 'x': 1, 'y': 2 }, { 'x': 2, 'y': 1 }];
   * var others = [{ 'x': 1, 'y': 1 }, { 'x': 1, 'y': 2 }];
   *
   * _.xorWith(objects, others, _.isEqual);
   * // => [{ 'x': 2, 'y': 1 }, { 'x': 1, 'y': 1 }]
   */
  var xorWith = baseRest(function(arrays) {
    var comparator = last(arrays)
    comparator = typeof comparator == 'function' ? comparator : undefined
    return baseXor(
      arrayFilter(arrays, isArrayLikeObject),
      undefined,
      comparator
    )
  })

  /**
   * Creates an array of grouped elements, the first of which contains the
   * first elements of the given arrays, the second of which contains the
   * second elements of the given arrays, and so on.
   *
   * @static
   * @memberOf _
   * @since 0.1.0
   * @category Array
   * @param {...Array} [arrays] The arrays to process.
   * @returns {Array} Returns the new array of grouped elements.
   * @example
   *
   * _.zip(['a', 'b'], [1, 2], [true, false]);
   * // => [['a', 1, true], ['b', 2, false]]
   */
  var zip = baseRest(unzip)

  /**
   * This base implementation of `_.zipObject` which assigns values using `assignFunc`.
   *
   * @private
   * @param {Array} props The property identifiers.
   * @param {Array} values The property values.
   * @param {Function} assignFunc The function to assign values.
   * @returns {Object} Returns the new object.
   */
  function baseZipObject(props, values, assignFunc) {
    var index = -1,
      length = props.length,
      valsLength = values.length,
      result = {}

    while (++index < length) {
      var value = index < valsLength ? values[index] : undefined
      assignFunc(result, props[index], value)
    }
    return result
  }

  /**
   * This method is like `_.fromPairs` except that it accepts two arrays,
   * one of property identifiers and one of corresponding values.
   *
   * @static
   * @memberOf _
   * @since 0.4.0
   * @category Array
   * @param {Array} [props=[]] The property identifiers.
   * @param {Array} [values=[]] The property values.
   * @returns {Object} Returns the new object.
   * @example
   *
   * _.zipObject(['a', 'b'], [1, 2]);
   * // => { 'a': 1, 'b': 2 }
   */
  function zipObject(props, values) {
    return baseZipObject(props || [], values || [], assignValue)
  }

  /**
   * This method is like `_.zipObject` except that it supports property paths.
   *
   * @static
   * @memberOf _
   * @since 4.1.0
   * @category Array
   * @param {Array} [props=[]] The property identifiers.
   * @param {Array} [values=[]] The property values.
   * @returns {Object} Returns the new object.
   * @example
   *
   * _.zipObjectDeep(['a.b[0].c', 'a.b[1].d'], [1, 2]);
   * // => { 'a': { 'b': [{ 'c': 1 }, { 'd': 2 }] } }
   */
  function zipObjectDeep(props, values) {
    return baseZipObject(props || [], values || [], baseSet)
  }

  /**
   * This method is like `_.zip` except that it accepts `iteratee` to specify
   * how grouped values should be combined. The iteratee is invoked with the
   * elements of each group: (...group).
   *
   * @static
   * @memberOf _
   * @since 3.8.0
   * @category Array
   * @param {...Array} [arrays] The arrays to process.
   * @param {Function} [iteratee=_.identity] The function to combine
   *  grouped values.
   * @returns {Array} Returns the new array of grouped elements.
   * @example
   *
   * _.zipWith([1, 2], [10, 20], [100, 200], function(a, b, c) {
   *   return a + b + c;
   * });
   * // => [111, 222]
   */
  var zipWith = baseRest(function(arrays) {
    var length = arrays.length,
      iteratee = length > 1 ? arrays[length - 1] : undefined

    iteratee =
      typeof iteratee == 'function' ? (arrays.pop(), iteratee) : undefined
    return unzipWith(arrays, iteratee)
  })

  var array = {
    chunk,
    compact,
    concat,
    difference,
    differenceBy,
    differenceWith,
    drop,
    dropRight,
    dropRightWhile,
    dropWhile,
    fill,
    findIndex,
    findLastIndex,
    first: head,
    flatten,
    flattenDeep,
    flattenDepth,
    fromPairs,
    head,
    indexOf,
    initial,
    intersection,
    intersectionBy,
    intersectionWith,
    join,
    last,
    lastIndexOf,
    nth,
    pull,
    pullAll,
    pullAllBy,
    pullAllWith,
    pullAt,
    remove,
    reverse,
    slice,
    sortedIndex,
    sortedIndexBy,
    sortedIndexOf,
    sortedLastIndex,
    sortedLastIndexBy,
    sortedLastIndexOf,
    sortedUniq,
    sortedUniqBy,
    tail,
    take,
    takeRight,
    takeRightWhile,
    takeWhile,
    union,
    unionBy,
    unionWith,
    uniq,
    uniqBy,
    uniqWith,
    unzip,
    unzipWith,
    without,
    xor,
    xorBy,
    xorWith,
    zip,
    zipObject,
    zipObjectDeep,
    zipWith,
  }

  var collection = {
    countBy,
    each: forEach,
    eachRight: forEachRight,
    every,
    filter,
    find,
    findLast,
    flatMap,
    flatMapDeep,
    flatMapDepth,
    forEach,
    forEachRight,
    groupBy,
    includes,
    invokeMap,
    keyBy,
    map,
    orderBy,
    partition,
    reduce,
    reduceRight,
    reject,
    sample,
    sampleSize,
    shuffle,
    size,
    some,
    sortBy,
  }

  var date$1 = {
    now,
  }

  var func = {
    after,
    ary,
    before,
    bind,
    bindKey,
    curry,
    curryRight,
    debounce,
    defer,
    delay,
    flip,
    memoize,
    negate,
    once,
    overArgs,
    partial,
    partialRight,
    rearg,
    rest,
    spread,
    throttle,
    unary,
    wrap,
  }

  var lang = {
    castArray,
    clone,
    cloneDeep,
    cloneDeepWith,
    cloneWith,
    conformsTo,
    eq: eq$1,
    gt: gt$1,
    gte: gte$1,
    isArguments,
    isArray,
    isArrayBuffer,
    isArrayLike,
    isArrayLikeObject,
    isBoolean,
    isBuffer,
    isDate,
    isElement,
    isEmpty,
    isEqual,
    isEqualWith,
    isError,
    isFinite: isFinite$1,
    isFunction,
    isInteger,
    isLength,
    isMap,
    isMatch,
    isMatchWith,
    isNaN: isNaN$1,
    isNative,
    isNil,
    isNull,
    isNumber,
    isObject,
    isObjectLike,
    isPlainObject,
    isRegExp,
    isSafeInteger,
    isSet,
    isString,
    isSymbol,
    isTypedArray,
    isUndefined,
    isWeakMap,
    isWeakSet,
    lt: lt$1,
    lte: lte$1,
    toArray,
    toFinite,
    toInteger,
    toLength,
    toNumber,
    toPlainObject,
    toSafeInteger,
    toString,
  }

  var math = {
    add: add$1,
    ceil: ceil$1,
    divide,
    floor,
    max: max$1,
    maxBy,
    mean,
    meanBy,
    min: min$1,
    minBy,
    multiply,
    round,
    subtract: subtract$1,
    sum,
    sumBy,
  }

  var number = {
    clamp,
    inRange: inRange$1,
    random,
  }

  var object = {
    assign,
    assignIn,
    assignInWith,
    assignWith,
    at,
    create,
    defaults,
    defaultsDeep,
    entries: toPairs,
    entriesIn: toPairsIn,
    extend: assignIn,
    extendWith: assignInWith,
    findKey,
    findLastKey,
    forIn,
    forInRight,
    forOwn,
    forOwnRight,
    functions,
    functionsIn,
    get,
    has: has$2,
    hasIn,
    invert,
    invertBy,
    invoke,
    keys,
    keysIn: keysIn$1,
    mapKeys,
    mapValues,
    merge: merge$1,
    mergeWith,
    omit,
    omitBy,
    pick,
    pickBy,
    result,
    set,
    setWith,
    toPairs,
    toPairsIn,
    transform,
    unset,
    update,
    updateWith,
    values,
    valuesIn,
  }

  var seq = {
    at: wrapperAt,
    chain,
    commit: wrapperCommit,
    lodash,
    next: wrapperNext,
    plant: wrapperPlant,
    reverse: wrapperReverse,
    tap,
    thru,
    toIterator: wrapperToIterator,
    toJSON: wrapperValue,
    value: wrapperValue,
    valueOf: wrapperValue,
    wrapperChain,
  }

  var string = {
    camelCase,
    capitalize,
    deburr,
    endsWith,
    escape,
    escapeRegExp,
    kebabCase,
    lowerCase,
    lowerFirst,
    pad,
    padEnd,
    padStart,
    parseInt: parseInt$1,
    repeat,
    replace,
    snakeCase,
    split,
    startCase,
    startsWith,
    template,
    templateSettings,
    toLower,
    toUpper,
    trim,
    trimEnd,
    trimStart,
    truncate,
    unescape,
    upperCase,
    upperFirst,
    words,
  }

  var util = {
    attempt,
    bindAll,
    cond,
    conforms,
    constant,
    defaultTo,
    flow,
    flowRight,
    identity,
    iteratee,
    matches,
    matchesProperty,
    method,
    methodOf,
    mixin,
    noop: noop$1,
    nthArg,
    over,
    overEvery,
    overSome,
    property,
    propertyOf,
    range: range$1,
    rangeRight,
    stubArray,
    stubFalse,
    stubObject,
    stubString,
    stubTrue,
    times,
    toPath,
    uniqueId,
  }

  /**
   * Creates a clone of the lazy wrapper object.
   *
   * @private
   * @name clone
   * @memberOf LazyWrapper
   * @returns {Object} Returns the cloned `LazyWrapper` object.
   */
  function lazyClone() {
    var result = new LazyWrapper(this.__wrapped__)
    result.__actions__ = copyArray(this.__actions__)
    result.__dir__ = this.__dir__
    result.__filtered__ = this.__filtered__
    result.__iteratees__ = copyArray(this.__iteratees__)
    result.__takeCount__ = this.__takeCount__
    result.__views__ = copyArray(this.__views__)
    return result
  }

  /**
   * Reverses the direction of lazy iteration.
   *
   * @private
   * @name reverse
   * @memberOf LazyWrapper
   * @returns {Object} Returns the new reversed `LazyWrapper` object.
   */
  function lazyReverse() {
    if (this.__filtered__) {
      var result = new LazyWrapper(this)
      result.__dir__ = -1
      result.__filtered__ = true
    } else {
      result = this.clone()
      result.__dir__ *= -1
    }
    return result
  }

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$f = Math.max,
    nativeMin$c = Math.min

  /**
   * Gets the view, applying any `transforms` to the `start` and `end` positions.
   *
   * @private
   * @param {number} start The start of the view.
   * @param {number} end The end of the view.
   * @param {Array} transforms The transformations to apply to the view.
   * @returns {Object} Returns an object containing the `start` and `end`
   *  positions of the view.
   */
  function getView(start, end, transforms) {
    var index = -1,
      length = transforms.length

    while (++index < length) {
      var data = transforms[index],
        size = data.size

      switch (data.type) {
        case 'drop':
          start += size
          break
        case 'dropRight':
          end -= size
          break
        case 'take':
          end = nativeMin$c(end, start + size)
          break
        case 'takeRight':
          start = nativeMax$f(start, end - size)
          break
      }
    }
    return { start: start, end: end }
  }

  /** Used to indicate the type of lazy iteratees. */
  var LAZY_FILTER_FLAG = 1,
    LAZY_MAP_FLAG = 2

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMin$d = Math.min

  /**
   * Extracts the unwrapped value from its lazy wrapper.
   *
   * @private
   * @name value
   * @memberOf LazyWrapper
   * @returns {*} Returns the unwrapped value.
   */
  function lazyValue() {
    var array = this.__wrapped__.value(),
      dir = this.__dir__,
      isArr = isArray(array),
      isRight = dir < 0,
      arrLength = isArr ? array.length : 0,
      view = getView(0, arrLength, this.__views__),
      start = view.start,
      end = view.end,
      length = end - start,
      index = isRight ? end : start - 1,
      iteratees = this.__iteratees__,
      iterLength = iteratees.length,
      resIndex = 0,
      takeCount = nativeMin$d(length, this.__takeCount__)

    if (!isArr || (!isRight && arrLength == length && takeCount == length)) {
      return baseWrapperValue(array, this.__actions__)
    }
    var result = []

    outer: while (length-- && resIndex < takeCount) {
      index += dir

      var iterIndex = -1,
        value = array[index]

      while (++iterIndex < iterLength) {
        var data = iteratees[iterIndex],
          iteratee = data.iteratee,
          type = data.type,
          computed = iteratee(value)

        if (type == LAZY_MAP_FLAG) {
          value = computed
        } else if (!computed) {
          if (type == LAZY_FILTER_FLAG) {
            continue outer
          } else {
            break outer
          }
        }
      }
      result[resIndex++] = value
    }
    return result
  }

  /**
   * @license
   * Lodash (Custom Build) <https://lodash.com/>
   * Build: `lodash modularize exports="es" -o ./`
   * Copyright OpenJS Foundation and other contributors <https://openjsf.org/>
   * Released under MIT license <https://lodash.com/license>
   * Based on Underscore.js 1.8.3 <http://underscorejs.org/LICENSE>
   * Copyright Jeremy Ashkenas, DocumentCloud and Investigative Reporters & Editors
   */

  /** Used as the semantic version number. */
  var VERSION = '4.17.15'

  /** Used to compose bitmasks for function metadata. */
  var WRAP_BIND_KEY_FLAG$6 = 2

  /** Used to indicate the type of lazy iteratees. */
  var LAZY_FILTER_FLAG$1 = 1,
    LAZY_WHILE_FLAG = 3

  /** Used as references for the maximum length and index of an array. */
  var MAX_ARRAY_LENGTH$6 = 4294967295

  /** Used for built-in method references. */
  var arrayProto$5 = Array.prototype,
    objectProto$s = Object.prototype

  /** Used to check objects for own properties. */
  var hasOwnProperty$p = objectProto$s.hasOwnProperty

  /** Built-in value references. */
  var symIterator$1 = Symbol$1 ? Symbol$1.iterator : undefined

  /* Built-in method references for those with the same name as other `lodash` methods. */
  var nativeMax$g = Math.max,
    nativeMin$e = Math.min

  // wrap `_.mixin` so it works when provided only one argument
  var mixin$1 = (function(func) {
    return function(object, source, options) {
      if (options == null) {
        var isObj = isObject(source),
          props = isObj && keys(source),
          methodNames = props && props.length && baseFunctions(source, props)

        if (!(methodNames ? methodNames.length : isObj)) {
          options = source
          source = object
          object = this
        }
      }
      return func(object, source, options)
    }
  })(mixin)

  // Add methods that return wrapped values in chain sequences.
  lodash.after = func.after
  lodash.ary = func.ary
  lodash.assign = object.assign
  lodash.assignIn = object.assignIn
  lodash.assignInWith = object.assignInWith
  lodash.assignWith = object.assignWith
  lodash.at = object.at
  lodash.before = func.before
  lodash.bind = func.bind
  lodash.bindAll = util.bindAll
  lodash.bindKey = func.bindKey
  lodash.castArray = lang.castArray
  lodash.chain = seq.chain
  lodash.chunk = array.chunk
  lodash.compact = array.compact
  lodash.concat = array.concat
  lodash.cond = util.cond
  lodash.conforms = util.conforms
  lodash.constant = util.constant
  lodash.countBy = collection.countBy
  lodash.create = object.create
  lodash.curry = func.curry
  lodash.curryRight = func.curryRight
  lodash.debounce = func.debounce
  lodash.defaults = object.defaults
  lodash.defaultsDeep = object.defaultsDeep
  lodash.defer = func.defer
  lodash.delay = func.delay
  lodash.difference = array.difference
  lodash.differenceBy = array.differenceBy
  lodash.differenceWith = array.differenceWith
  lodash.drop = array.drop
  lodash.dropRight = array.dropRight
  lodash.dropRightWhile = array.dropRightWhile
  lodash.dropWhile = array.dropWhile
  lodash.fill = array.fill
  lodash.filter = collection.filter
  lodash.flatMap = collection.flatMap
  lodash.flatMapDeep = collection.flatMapDeep
  lodash.flatMapDepth = collection.flatMapDepth
  lodash.flatten = array.flatten
  lodash.flattenDeep = array.flattenDeep
  lodash.flattenDepth = array.flattenDepth
  lodash.flip = func.flip
  lodash.flow = util.flow
  lodash.flowRight = util.flowRight
  lodash.fromPairs = array.fromPairs
  lodash.functions = object.functions
  lodash.functionsIn = object.functionsIn
  lodash.groupBy = collection.groupBy
  lodash.initial = array.initial
  lodash.intersection = array.intersection
  lodash.intersectionBy = array.intersectionBy
  lodash.intersectionWith = array.intersectionWith
  lodash.invert = object.invert
  lodash.invertBy = object.invertBy
  lodash.invokeMap = collection.invokeMap
  lodash.iteratee = util.iteratee
  lodash.keyBy = collection.keyBy
  lodash.keys = keys
  lodash.keysIn = object.keysIn
  lodash.map = collection.map
  lodash.mapKeys = object.mapKeys
  lodash.mapValues = object.mapValues
  lodash.matches = util.matches
  lodash.matchesProperty = util.matchesProperty
  lodash.memoize = func.memoize
  lodash.merge = object.merge
  lodash.mergeWith = object.mergeWith
  lodash.method = util.method
  lodash.methodOf = util.methodOf
  lodash.mixin = mixin$1
  lodash.negate = negate
  lodash.nthArg = util.nthArg
  lodash.omit = object.omit
  lodash.omitBy = object.omitBy
  lodash.once = func.once
  lodash.orderBy = collection.orderBy
  lodash.over = util.over
  lodash.overArgs = func.overArgs
  lodash.overEvery = util.overEvery
  lodash.overSome = util.overSome
  lodash.partial = func.partial
  lodash.partialRight = func.partialRight
  lodash.partition = collection.partition
  lodash.pick = object.pick
  lodash.pickBy = object.pickBy
  lodash.property = util.property
  lodash.propertyOf = util.propertyOf
  lodash.pull = array.pull
  lodash.pullAll = array.pullAll
  lodash.pullAllBy = array.pullAllBy
  lodash.pullAllWith = array.pullAllWith
  lodash.pullAt = array.pullAt
  lodash.range = util.range
  lodash.rangeRight = util.rangeRight
  lodash.rearg = func.rearg
  lodash.reject = collection.reject
  lodash.remove = array.remove
  lodash.rest = func.rest
  lodash.reverse = array.reverse
  lodash.sampleSize = collection.sampleSize
  lodash.set = object.set
  lodash.setWith = object.setWith
  lodash.shuffle = collection.shuffle
  lodash.slice = array.slice
  lodash.sortBy = collection.sortBy
  lodash.sortedUniq = array.sortedUniq
  lodash.sortedUniqBy = array.sortedUniqBy
  lodash.split = string.split
  lodash.spread = func.spread
  lodash.tail = array.tail
  lodash.take = array.take
  lodash.takeRight = array.takeRight
  lodash.takeRightWhile = array.takeRightWhile
  lodash.takeWhile = array.takeWhile
  lodash.tap = seq.tap
  lodash.throttle = func.throttle
  lodash.thru = thru
  lodash.toArray = lang.toArray
  lodash.toPairs = object.toPairs
  lodash.toPairsIn = object.toPairsIn
  lodash.toPath = util.toPath
  lodash.toPlainObject = lang.toPlainObject
  lodash.transform = object.transform
  lodash.unary = func.unary
  lodash.union = array.union
  lodash.unionBy = array.unionBy
  lodash.unionWith = array.unionWith
  lodash.uniq = array.uniq
  lodash.uniqBy = array.uniqBy
  lodash.uniqWith = array.uniqWith
  lodash.unset = object.unset
  lodash.unzip = array.unzip
  lodash.unzipWith = array.unzipWith
  lodash.update = object.update
  lodash.updateWith = object.updateWith
  lodash.values = object.values
  lodash.valuesIn = object.valuesIn
  lodash.without = array.without
  lodash.words = string.words
  lodash.wrap = func.wrap
  lodash.xor = array.xor
  lodash.xorBy = array.xorBy
  lodash.xorWith = array.xorWith
  lodash.zip = array.zip
  lodash.zipObject = array.zipObject
  lodash.zipObjectDeep = array.zipObjectDeep
  lodash.zipWith = array.zipWith

  // Add aliases.
  lodash.entries = object.toPairs
  lodash.entriesIn = object.toPairsIn
  lodash.extend = object.assignIn
  lodash.extendWith = object.assignInWith

  // Add methods to `lodash.prototype`.
  mixin$1(lodash, lodash)

  // Add methods that return unwrapped values in chain sequences.
  lodash.add = math.add
  lodash.attempt = util.attempt
  lodash.camelCase = string.camelCase
  lodash.capitalize = string.capitalize
  lodash.ceil = math.ceil
  lodash.clamp = number.clamp
  lodash.clone = lang.clone
  lodash.cloneDeep = lang.cloneDeep
  lodash.cloneDeepWith = lang.cloneDeepWith
  lodash.cloneWith = lang.cloneWith
  lodash.conformsTo = lang.conformsTo
  lodash.deburr = string.deburr
  lodash.defaultTo = util.defaultTo
  lodash.divide = math.divide
  lodash.endsWith = string.endsWith
  lodash.eq = lang.eq
  lodash.escape = string.escape
  lodash.escapeRegExp = string.escapeRegExp
  lodash.every = collection.every
  lodash.find = collection.find
  lodash.findIndex = array.findIndex
  lodash.findKey = object.findKey
  lodash.findLast = collection.findLast
  lodash.findLastIndex = array.findLastIndex
  lodash.findLastKey = object.findLastKey
  lodash.floor = math.floor
  lodash.forEach = collection.forEach
  lodash.forEachRight = collection.forEachRight
  lodash.forIn = object.forIn
  lodash.forInRight = object.forInRight
  lodash.forOwn = object.forOwn
  lodash.forOwnRight = object.forOwnRight
  lodash.get = object.get
  lodash.gt = lang.gt
  lodash.gte = lang.gte
  lodash.has = object.has
  lodash.hasIn = object.hasIn
  lodash.head = array.head
  lodash.identity = identity
  lodash.includes = collection.includes
  lodash.indexOf = array.indexOf
  lodash.inRange = number.inRange
  lodash.invoke = object.invoke
  lodash.isArguments = lang.isArguments
  lodash.isArray = isArray
  lodash.isArrayBuffer = lang.isArrayBuffer
  lodash.isArrayLike = lang.isArrayLike
  lodash.isArrayLikeObject = lang.isArrayLikeObject
  lodash.isBoolean = lang.isBoolean
  lodash.isBuffer = lang.isBuffer
  lodash.isDate = lang.isDate
  lodash.isElement = lang.isElement
  lodash.isEmpty = lang.isEmpty
  lodash.isEqual = lang.isEqual
  lodash.isEqualWith = lang.isEqualWith
  lodash.isError = lang.isError
  lodash.isFinite = lang.isFinite
  lodash.isFunction = lang.isFunction
  lodash.isInteger = lang.isInteger
  lodash.isLength = lang.isLength
  lodash.isMap = lang.isMap
  lodash.isMatch = lang.isMatch
  lodash.isMatchWith = lang.isMatchWith
  lodash.isNaN = lang.isNaN
  lodash.isNative = lang.isNative
  lodash.isNil = lang.isNil
  lodash.isNull = lang.isNull
  lodash.isNumber = lang.isNumber
  lodash.isObject = isObject
  lodash.isObjectLike = lang.isObjectLike
  lodash.isPlainObject = lang.isPlainObject
  lodash.isRegExp = lang.isRegExp
  lodash.isSafeInteger = lang.isSafeInteger
  lodash.isSet = lang.isSet
  lodash.isString = lang.isString
  lodash.isSymbol = lang.isSymbol
  lodash.isTypedArray = lang.isTypedArray
  lodash.isUndefined = lang.isUndefined
  lodash.isWeakMap = lang.isWeakMap
  lodash.isWeakSet = lang.isWeakSet
  lodash.join = array.join
  lodash.kebabCase = string.kebabCase
  lodash.last = last
  lodash.lastIndexOf = array.lastIndexOf
  lodash.lowerCase = string.lowerCase
  lodash.lowerFirst = string.lowerFirst
  lodash.lt = lang.lt
  lodash.lte = lang.lte
  lodash.max = math.max
  lodash.maxBy = math.maxBy
  lodash.mean = math.mean
  lodash.meanBy = math.meanBy
  lodash.min = math.min
  lodash.minBy = math.minBy
  lodash.stubArray = util.stubArray
  lodash.stubFalse = util.stubFalse
  lodash.stubObject = util.stubObject
  lodash.stubString = util.stubString
  lodash.stubTrue = util.stubTrue
  lodash.multiply = math.multiply
  lodash.nth = array.nth
  lodash.noop = util.noop
  lodash.now = date$1.now
  lodash.pad = string.pad
  lodash.padEnd = string.padEnd
  lodash.padStart = string.padStart
  lodash.parseInt = string.parseInt
  lodash.random = number.random
  lodash.reduce = collection.reduce
  lodash.reduceRight = collection.reduceRight
  lodash.repeat = string.repeat
  lodash.replace = string.replace
  lodash.result = object.result
  lodash.round = math.round
  lodash.sample = collection.sample
  lodash.size = collection.size
  lodash.snakeCase = string.snakeCase
  lodash.some = collection.some
  lodash.sortedIndex = array.sortedIndex
  lodash.sortedIndexBy = array.sortedIndexBy
  lodash.sortedIndexOf = array.sortedIndexOf
  lodash.sortedLastIndex = array.sortedLastIndex
  lodash.sortedLastIndexBy = array.sortedLastIndexBy
  lodash.sortedLastIndexOf = array.sortedLastIndexOf
  lodash.startCase = string.startCase
  lodash.startsWith = string.startsWith
  lodash.subtract = math.subtract
  lodash.sum = math.sum
  lodash.sumBy = math.sumBy
  lodash.template = string.template
  lodash.times = util.times
  lodash.toFinite = lang.toFinite
  lodash.toInteger = toInteger
  lodash.toLength = lang.toLength
  lodash.toLower = string.toLower
  lodash.toNumber = lang.toNumber
  lodash.toSafeInteger = lang.toSafeInteger
  lodash.toString = lang.toString
  lodash.toUpper = string.toUpper
  lodash.trim = string.trim
  lodash.trimEnd = string.trimEnd
  lodash.trimStart = string.trimStart
  lodash.truncate = string.truncate
  lodash.unescape = string.unescape
  lodash.uniqueId = util.uniqueId
  lodash.upperCase = string.upperCase
  lodash.upperFirst = string.upperFirst

  // Add aliases.
  lodash.each = collection.forEach
  lodash.eachRight = collection.forEachRight
  lodash.first = array.head

  mixin$1(
    lodash,
    (function() {
      var source = {}
      baseForOwn(lodash, function(func, methodName) {
        if (!hasOwnProperty$p.call(lodash.prototype, methodName)) {
          source[methodName] = func
        }
      })
      return source
    })(),
    { chain: false }
  )

  /**
   * The semantic version number.
   *
   * @static
   * @memberOf _
   * @type {string}
   */
  lodash.VERSION = VERSION
  ;(lodash.templateSettings = string.templateSettings).imports._ = lodash

  // Assign default placeholders.
  arrayEach(
    ['bind', 'bindKey', 'curry', 'curryRight', 'partial', 'partialRight'],
    function(methodName) {
      lodash[methodName].placeholder = lodash
    }
  )

  // Add `LazyWrapper` methods for `_.drop` and `_.take` variants.
  arrayEach(['drop', 'take'], function(methodName, index) {
    LazyWrapper.prototype[methodName] = function(n) {
      n = n === undefined ? 1 : nativeMax$g(toInteger(n), 0)

      var result =
        this.__filtered__ && !index ? new LazyWrapper(this) : this.clone()

      if (result.__filtered__) {
        result.__takeCount__ = nativeMin$e(n, result.__takeCount__)
      } else {
        result.__views__.push({
          size: nativeMin$e(n, MAX_ARRAY_LENGTH$6),
          type: methodName + (result.__dir__ < 0 ? 'Right' : ''),
        })
      }
      return result
    }

    LazyWrapper.prototype[methodName + 'Right'] = function(n) {
      return this.reverse()
        [methodName](n)
        .reverse()
    }
  })

  // Add `LazyWrapper` methods that accept an `iteratee` value.
  arrayEach(['filter', 'map', 'takeWhile'], function(methodName, index) {
    var type = index + 1,
      isFilter = type == LAZY_FILTER_FLAG$1 || type == LAZY_WHILE_FLAG

    LazyWrapper.prototype[methodName] = function(iteratee) {
      var result = this.clone()
      result.__iteratees__.push({
        iteratee: baseIteratee(iteratee),
        type: type,
      })
      result.__filtered__ = result.__filtered__ || isFilter
      return result
    }
  })

  // Add `LazyWrapper` methods for `_.head` and `_.last`.
  arrayEach(['head', 'last'], function(methodName, index) {
    var takeName = 'take' + (index ? 'Right' : '')

    LazyWrapper.prototype[methodName] = function() {
      return this[takeName](1).value()[0]
    }
  })

  // Add `LazyWrapper` methods for `_.initial` and `_.tail`.
  arrayEach(['initial', 'tail'], function(methodName, index) {
    var dropName = 'drop' + (index ? '' : 'Right')

    LazyWrapper.prototype[methodName] = function() {
      return this.__filtered__ ? new LazyWrapper(this) : this[dropName](1)
    }
  })

  LazyWrapper.prototype.compact = function() {
    return this.filter(identity)
  }

  LazyWrapper.prototype.find = function(predicate) {
    return this.filter(predicate).head()
  }

  LazyWrapper.prototype.findLast = function(predicate) {
    return this.reverse().find(predicate)
  }

  LazyWrapper.prototype.invokeMap = baseRest(function(path, args) {
    if (typeof path == 'function') {
      return new LazyWrapper(this)
    }
    return this.map(function(value) {
      return baseInvoke(value, path, args)
    })
  })

  LazyWrapper.prototype.reject = function(predicate) {
    return this.filter(negate(baseIteratee(predicate)))
  }

  LazyWrapper.prototype.slice = function(start, end) {
    start = toInteger(start)

    var result = this
    if (result.__filtered__ && (start > 0 || end < 0)) {
      return new LazyWrapper(result)
    }
    if (start < 0) {
      result = result.takeRight(-start)
    } else if (start) {
      result = result.drop(start)
    }
    if (end !== undefined) {
      end = toInteger(end)
      result = end < 0 ? result.dropRight(-end) : result.take(end - start)
    }
    return result
  }

  LazyWrapper.prototype.takeRightWhile = function(predicate) {
    return this.reverse()
      .takeWhile(predicate)
      .reverse()
  }

  LazyWrapper.prototype.toArray = function() {
    return this.take(MAX_ARRAY_LENGTH$6)
  }

  // Add `LazyWrapper` methods to `lodash.prototype`.
  baseForOwn(LazyWrapper.prototype, function(func, methodName) {
    var checkIteratee = /^(?:filter|find|map|reject)|While$/.test(methodName),
      isTaker = /^(?:head|last)$/.test(methodName),
      lodashFunc =
        lodash[
          isTaker ? 'take' + (methodName == 'last' ? 'Right' : '') : methodName
        ],
      retUnwrapped = isTaker || /^find/.test(methodName)

    if (!lodashFunc) {
      return
    }
    lodash.prototype[methodName] = function() {
      var value = this.__wrapped__,
        args = isTaker ? [1] : arguments,
        isLazy = value instanceof LazyWrapper,
        iteratee = args[0],
        useLazy = isLazy || isArray(value)

      var interceptor = function(value) {
        var result = lodashFunc.apply(lodash, arrayPush([value], args))
        return isTaker && chainAll ? result[0] : result
      }

      if (
        useLazy &&
        checkIteratee &&
        typeof iteratee == 'function' &&
        iteratee.length != 1
      ) {
        // Avoid lazy use if the iteratee has a "length" value other than `1`.
        isLazy = useLazy = false
      }
      var chainAll = this.__chain__,
        isHybrid = !!this.__actions__.length,
        isUnwrapped = retUnwrapped && !chainAll,
        onlyLazy = isLazy && !isHybrid

      if (!retUnwrapped && useLazy) {
        value = onlyLazy ? value : new LazyWrapper(this)
        var result = func.apply(value, args)
        result.__actions__.push({
          func: thru,
          args: [interceptor],
          thisArg: undefined,
        })
        return new LodashWrapper(result, chainAll)
      }
      if (isUnwrapped && onlyLazy) {
        return func.apply(this, args)
      }
      result = this.thru(interceptor)
      return isUnwrapped
        ? isTaker
          ? result.value()[0]
          : result.value()
        : result
    }
  })

  // Add `Array` methods to `lodash.prototype`.
  arrayEach(['pop', 'push', 'shift', 'sort', 'splice', 'unshift'], function(
    methodName
  ) {
    var func = arrayProto$5[methodName],
      chainName = /^(?:push|sort|unshift)$/.test(methodName) ? 'tap' : 'thru',
      retUnwrapped = /^(?:pop|shift)$/.test(methodName)

    lodash.prototype[methodName] = function() {
      var args = arguments
      if (retUnwrapped && !this.__chain__) {
        var value = this.value()
        return func.apply(isArray(value) ? value : [], args)
      }
      return this[chainName](function(value) {
        return func.apply(isArray(value) ? value : [], args)
      })
    }
  })

  // Map minified method names to their real names.
  baseForOwn(LazyWrapper.prototype, function(func, methodName) {
    var lodashFunc = lodash[methodName]
    if (lodashFunc) {
      var key = lodashFunc.name + ''
      if (!hasOwnProperty$p.call(realNames, key)) {
        realNames[key] = []
      }
      realNames[key].push({ name: methodName, func: lodashFunc })
    }
  })

  realNames[createHybrid(undefined, WRAP_BIND_KEY_FLAG$6).name] = [
    {
      name: 'wrapper',
      func: undefined,
    },
  ]

  // Add methods to `LazyWrapper`.
  LazyWrapper.prototype.clone = lazyClone
  LazyWrapper.prototype.reverse = lazyReverse
  LazyWrapper.prototype.value = lazyValue

  // Add chain sequence methods to the `lodash` wrapper.
  lodash.prototype.at = seq.at
  lodash.prototype.chain = seq.wrapperChain
  lodash.prototype.commit = seq.commit
  lodash.prototype.next = seq.next
  lodash.prototype.plant = seq.plant
  lodash.prototype.reverse = seq.reverse
  lodash.prototype.toJSON = lodash.prototype.valueOf = lodash.prototype.value =
    seq.value

  // Add lazy aliases.
  lodash.prototype.first = lodash.prototype.head

  if (symIterator$1) {
    lodash.prototype[symIterator$1] = seq.toIterator
  }

  function ownerDocument(node) {
    return (node && node.ownerDocument) || document
  }

  function ownerWindow(node) {
    var doc = ownerDocument(node)
    return (doc && doc.defaultView) || window
  }

  function getComputedStyle$1(node, psuedoElement) {
    return ownerWindow(node).getComputedStyle(node, psuedoElement)
  }

  var rUpper = /([A-Z])/g
  function hyphenate(string) {
    return string.replace(rUpper, '-$1').toLowerCase()
  }

  /**
   * Copyright 2013-2014, Facebook, Inc.
   * All rights reserved.
   * https://github.com/facebook/react/blob/2aeb8a2a6beb00617a4217f7f8284924fa2ad819/src/vendor/core/hyphenateStyleName.js
   */
  var msPattern = /^ms-/
  function hyphenateStyleName(string) {
    return hyphenate(string).replace(msPattern, '-ms-')
  }

  var supportedTransforms = /^((translate|rotate|scale)(X|Y|Z|3d)?|matrix(3d)?|perspective|skew(X|Y)?)$/i
  function isTransform(value) {
    return !!(value && supportedTransforms.test(value))
  }

  function style(node, property) {
    var css = ''
    var transforms = ''

    if (typeof property === 'string') {
      return (
        node.style.getPropertyValue(hyphenateStyleName(property)) ||
        getComputedStyle$1(node).getPropertyValue(hyphenateStyleName(property))
      )
    }

    Object.keys(property).forEach(function(key) {
      var value = property[key]

      if (!value && value !== 0) {
        node.style.removeProperty(hyphenateStyleName(key))
      } else if (isTransform(key)) {
        transforms += key + '(' + value + ') '
      } else {
        css += hyphenateStyleName(key) + ': ' + value + ';'
      }
    })

    if (transforms) {
      css += 'transform: ' + transforms + ';'
    }

    node.style.cssText += ';' + css
  }

  /* eslint-disable no-bitwise, no-cond-assign */
  // HTML DOM and SVG DOM may have different support levels,
  // so we need to check on context instead of a document root element.
  function contains(context, node) {
    if (context.contains) return context.contains(node)
    if (context.compareDocumentPosition)
      return context === node || !!(context.compareDocumentPosition(node) & 16)
  }

  function isDocument(element) {
    return 'nodeType' in element && element.nodeType === document.DOCUMENT_NODE
  }

  function isWindow(node) {
    if ('window' in node && node.window === node) return node
    if (isDocument(node)) return node.defaultView || false
    return false
  }

  function getscrollAccessor(offset) {
    var prop = offset === 'pageXOffset' ? 'scrollLeft' : 'scrollTop'

    function scrollAccessor(node, val) {
      var win = isWindow(node)

      if (val === undefined) {
        return win ? win[offset] : node[prop]
      }

      if (win) {
        win.scrollTo(val, win[offset])
      } else {
        node[prop] = val
      }
    }

    return scrollAccessor
  }

  var getScrollLeft = getscrollAccessor('pageXOffset')

  var getScrollTop = getscrollAccessor('pageYOffset')

  function offset(node) {
    var doc = ownerDocument(node)
    var box = {
      top: 0,
      left: 0,
      height: 0,
      width: 0,
    }
    var docElem = doc && doc.documentElement // Make sure it's not a disconnected DOM node

    if (!docElem || !contains(docElem, node)) return box
    if (node.getBoundingClientRect !== undefined)
      box = node.getBoundingClientRect()
    box = {
      top: box.top + getScrollTop(node) - (docElem.clientTop || 0),
      left: box.left + getScrollLeft(node) - (docElem.clientLeft || 0),
      width: box.width,
      height: box.height,
    }
    return box
  }

  var isHTMLElement = function isHTMLElement(e) {
    return !!e && 'offsetParent' in e
  }

  function offsetParent(node) {
    var doc = ownerDocument(node)
    var parent = node && node.offsetParent

    while (
      isHTMLElement(parent) &&
      parent.nodeName !== 'HTML' &&
      style(parent, 'position') === 'static'
    ) {
      parent = parent.offsetParent
    }

    return parent || doc.documentElement
  }

  var nodeName = function nodeName(node) {
    return node.nodeName && node.nodeName.toLowerCase()
  }

  function position(node, offsetParent$1) {
    var parentOffset = {
      top: 0,
      left: 0,
    }
    var offset$1 // Fixed elements are offset from window (parentOffset = {top:0, left: 0},
    // because it is its only offset parent

    if (style(node, 'position') === 'fixed') {
      offset$1 = node.getBoundingClientRect()
    } else {
      var parent = offsetParent$1 || offsetParent(node)
      offset$1 = offset(node)
      if (nodeName(parent) !== 'html') parentOffset = offset(parent)
      var borderTop = String(style(parent, 'borderTopWidth') || 0)
      parentOffset.top += parseInt(borderTop, 10) - getScrollTop(parent) || 0
      var borderLeft = String(style(parent, 'borderLeftWidth') || 0)
      parentOffset.left += parseInt(borderLeft, 10) - getScrollLeft(parent) || 0
    }

    var marginTop = String(style(node, 'marginTop') || 0)
    var marginLeft = String(style(node, 'marginLeft') || 0) // Subtract parent offsets and node margins

    return _extends({}, offset$1, {
      top: offset$1.top - parentOffset.top - (parseInt(marginTop, 10) || 0),
      left: offset$1.left - parentOffset.left - (parseInt(marginLeft, 10) || 0),
    })
  }

  var canUseDOM = !!(
    typeof window !== 'undefined' &&
    window.document &&
    window.document.createElement
  )

  /* https://github.com/component/raf */
  var prev = new Date().getTime()

  function fallback(fn) {
    var curr = new Date().getTime()
    var ms = Math.max(0, 16 - (curr - prev))
    var handle = setTimeout(fn, ms)
    prev = curr
    return handle
  }

  var vendors = ['', 'webkit', 'moz', 'o', 'ms']
  var cancelMethod = 'clearTimeout'
  var rafImpl = fallback // eslint-disable-next-line import/no-mutable-exports

  var getKey = function getKey(vendor, k) {
    return (
      vendor +
      (!vendor ? k : k[0].toUpperCase() + k.substr(1)) +
      'AnimationFrame'
    )
  }

  if (canUseDOM) {
    vendors.some(function(vendor) {
      var rafMethod = getKey(vendor, 'request')

      if (rafMethod in window) {
        cancelMethod = getKey(vendor, 'cancel') // @ts-ignore

        rafImpl = function rafImpl(cb) {
          return window[rafMethod](cb)
        }
      }

      return !!rafImpl
    })
  }

  var cancel = function cancel(id) {
    // @ts-ignore
    if (typeof window[cancelMethod] === 'function') window[cancelMethod](id)
  }
  var request = rafImpl

  var EventCell =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(EventCell, _React$Component)

      function EventCell() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = EventCell.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          style = _this$props.style,
          className = _this$props.className,
          event = _this$props.event,
          selected = _this$props.selected,
          isAllDay = _this$props.isAllDay,
          onSelect = _this$props.onSelect,
          _onDoubleClick = _this$props.onDoubleClick,
          localizer = _this$props.localizer,
          continuesPrior = _this$props.continuesPrior,
          continuesAfter = _this$props.continuesAfter,
          accessors = _this$props.accessors,
          getters = _this$props.getters,
          children = _this$props.children,
          _this$props$component = _this$props.components,
          Event = _this$props$component.event,
          EventWrapper = _this$props$component.eventWrapper,
          slotStart = _this$props.slotStart,
          slotEnd = _this$props.slotEnd,
          props = _objectWithoutPropertiesLoose(_this$props, [
            'style',
            'className',
            'event',
            'selected',
            'isAllDay',
            'onSelect',
            'onDoubleClick',
            'localizer',
            'continuesPrior',
            'continuesAfter',
            'accessors',
            'getters',
            'children',
            'components',
            'slotStart',
            'slotEnd',
          ])

        var title = accessors.title(event)
        var tooltip = accessors.tooltip(event)
        var end = accessors.end(event)
        var start = accessors.start(event)
        var allDay = accessors.allDay(event)
        var showAsAllDay =
          isAllDay || allDay || diff(start, ceil(end, 'day'), 'day') > 1
        var userProps = getters.eventProp(event, start, end, selected)
        var content = React__default.createElement(
          'div',
          {
            className: 'rbc-event-content',
            title: tooltip || undefined,
          },
          Event
            ? React__default.createElement(Event, {
                event: event,
                continuesPrior: continuesPrior,
                continuesAfter: continuesAfter,
                title: title,
                isAllDay: allDay,
                localizer: localizer,
                slotStart: slotStart,
                slotEnd: slotEnd,
              })
            : title
        )
        return React__default.createElement(
          EventWrapper,
          _extends({}, this.props, {
            type: 'date',
          }),
          React__default.createElement(
            'div',
            _extends({}, props, {
              tabIndex: 0,
              style: _extends({}, userProps.style, {}, style),
              className: clsx('rbc-event', className, userProps.className, {
                'rbc-selected': selected,
                'rbc-event-allday': showAsAllDay,
                'rbc-event-continues-prior': continuesPrior,
                'rbc-event-continues-after': continuesAfter,
              }),
              onClick: function onClick(e) {
                return onSelect && onSelect(event, e)
              },
              onDoubleClick: function onDoubleClick(e) {
                return _onDoubleClick && _onDoubleClick(event, e)
              },
            }),
            typeof children === 'function' ? children(content) : content
          )
        )
      }

      return EventCell
    })(React__default.Component)

  EventCell.propTypes = {
    event: propTypes.object.isRequired,
    slotStart: propTypes.instanceOf(Date),
    slotEnd: propTypes.instanceOf(Date),
    selected: propTypes.bool,
    isAllDay: propTypes.bool,
    continuesPrior: propTypes.bool,
    continuesAfter: propTypes.bool,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object,
    onSelect: propTypes.func,
    onDoubleClick: propTypes.func,
  }

  function isSelected(event, selected) {
    if (!event || selected == null) return false
    return [].concat(selected).indexOf(event) !== -1
  }
  function slotWidth(rowBox, slots) {
    var rowWidth = rowBox.right - rowBox.left
    var cellWidth = rowWidth / slots
    return cellWidth
  }
  function getSlotAtX(rowBox, x, rtl, slots) {
    var cellWidth = slotWidth(rowBox, slots)
    return rtl
      ? slots - 1 - Math.floor((x - rowBox.left) / cellWidth)
      : Math.floor((x - rowBox.left) / cellWidth)
  }
  function pointInBox(box, _ref) {
    var x = _ref.x,
      y = _ref.y
    return y >= box.top && y <= box.bottom && x >= box.left && x <= box.right
  }
  function dateCellSelection(start, rowBox, box, slots, rtl) {
    var startIdx = -1
    var endIdx = -1
    var lastSlotIdx = slots - 1
    var cellWidth = slotWidth(rowBox, slots) // cell under the mouse

    var currentSlot = getSlotAtX(rowBox, box.x, rtl, slots) // Identify row as either the initial row
    // or the row under the current mouse point

    var isCurrentRow = rowBox.top < box.y && rowBox.bottom > box.y
    var isStartRow = rowBox.top < start.y && rowBox.bottom > start.y // this row's position relative to the start point

    var isAboveStart = start.y > rowBox.bottom
    var isBelowStart = rowBox.top > start.y
    var isBetween = box.top < rowBox.top && box.bottom > rowBox.bottom // this row is between the current and start rows, so entirely selected

    if (isBetween) {
      startIdx = 0
      endIdx = lastSlotIdx
    }

    if (isCurrentRow) {
      if (isBelowStart) {
        startIdx = 0
        endIdx = currentSlot
      } else if (isAboveStart) {
        startIdx = currentSlot
        endIdx = lastSlotIdx
      }
    }

    if (isStartRow) {
      // select the cell under the initial point
      startIdx = endIdx = rtl
        ? lastSlotIdx - Math.floor((start.x - rowBox.left) / cellWidth)
        : Math.floor((start.x - rowBox.left) / cellWidth)

      if (isCurrentRow) {
        if (currentSlot < startIdx) startIdx = currentSlot
        else endIdx = currentSlot //select current range
      } else if (start.y < box.y) {
        // the current row is below start row
        // select cells to the right of the start cell
        endIdx = lastSlotIdx
      } else {
        // select cells to the left of the start cell
        startIdx = 0
      }
    }

    return {
      startIdx: startIdx,
      endIdx: endIdx,
    }
  }

  var Popup =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Popup, _React$Component)

      function Popup() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = Popup.prototype

      _proto.componentDidMount = function componentDidMount() {
        var _this$props = this.props,
          _this$props$popupOffs = _this$props.popupOffset,
          popupOffset =
            _this$props$popupOffs === void 0 ? 5 : _this$props$popupOffs,
          popperRef = _this$props.popperRef,
          _getOffset = offset(popperRef.current),
          top = _getOffset.top,
          left = _getOffset.left,
          width = _getOffset.width,
          height = _getOffset.height,
          viewBottom = window.innerHeight + getScrollTop(window),
          viewRight = window.innerWidth + getScrollLeft(window),
          bottom = top + height,
          right = left + width

        if (bottom > viewBottom || right > viewRight) {
          var topOffset, leftOffset
          if (bottom > viewBottom)
            topOffset =
              bottom - viewBottom + (popupOffset.y || +popupOffset || 0)
          if (right > viewRight)
            leftOffset =
              right - viewRight + (popupOffset.x || +popupOffset || 0)
          this.setState({
            topOffset: topOffset,
            leftOffset: leftOffset,
          }) //eslint-disable-line
        }
      }

      _proto.render = function render() {
        var _this$props2 = this.props,
          events = _this$props2.events,
          selected = _this$props2.selected,
          getters = _this$props2.getters,
          accessors = _this$props2.accessors,
          components = _this$props2.components,
          onSelect = _this$props2.onSelect,
          onDoubleClick = _this$props2.onDoubleClick,
          slotStart = _this$props2.slotStart,
          slotEnd = _this$props2.slotEnd,
          localizer = _this$props2.localizer,
          popperRef = _this$props2.popperRef
        var width = this.props.position.width,
          topOffset = (this.state || {}).topOffset || 0,
          leftOffset = (this.state || {}).leftOffset || 0
        var style = {
          top: -topOffset,
          left: -leftOffset,
          minWidth: width + width / 2,
        }
        return React__default.createElement(
          'div',
          {
            style: _extends({}, this.props.style, {}, style),
            className: 'rbc-overlay',
            ref: popperRef,
          },
          React__default.createElement(
            'div',
            {
              className: 'rbc-overlay-header',
            },
            localizer.format(slotStart, 'dayHeaderFormat')
          ),
          events.map(function(event, idx) {
            return React__default.createElement(EventCell, {
              key: idx,
              type: 'popup',
              event: event,
              getters: getters,
              onSelect: onSelect,
              accessors: accessors,
              components: components,
              onDoubleClick: onDoubleClick,
              continuesPrior: lt(accessors.end(event), slotStart, 'day'),
              continuesAfter: gte(accessors.start(event), slotEnd, 'day'),
              slotStart: slotStart,
              slotEnd: slotEnd,
              selected: isSelected(event, selected),
            })
          })
        )
      }

      return Popup
    })(React__default.Component)

  Popup.propTypes = {
    position: propTypes.object,
    popupOffset: propTypes.oneOfType([
      propTypes.number,
      propTypes.shape({
        x: propTypes.number,
        y: propTypes.number,
      }),
    ]),
    events: propTypes.array,
    selected: propTypes.object,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    onSelect: propTypes.func,
    onDoubleClick: propTypes.func,
    slotStart: propTypes.instanceOf(Date),
    slotEnd: propTypes.number,
    popperRef: propTypes.oneOfType([
      propTypes.func,
      propTypes.shape({
        current: propTypes.Element,
      }),
    ]),
  }
  /**
   * The Overlay component, of react-overlays, creates a ref that is passed to the Popup, and
   * requires proper ref forwarding to be used without error
   */

  var Popup$1 = React__default.forwardRef(function(props, ref) {
    return React__default.createElement(
      Popup,
      _extends(
        {
          popperRef: ref,
        },
        props
      )
    )
  })

  /**!
   * @fileOverview Kickass library to create and place poppers near their reference elements.
   * @version 1.15.0
   * @license
   * Copyright (c) 2016 Federico Zivolo and contributors
   *
   * Permission is hereby granted, free of charge, to any person obtaining a copy
   * of this software and associated documentation files (the "Software"), to deal
   * in the Software without restriction, including without limitation the rights
   * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   * copies of the Software, and to permit persons to whom the Software is
   * furnished to do so, subject to the following conditions:
   *
   * The above copyright notice and this permission notice shall be included in all
   * copies or substantial portions of the Software.
   *
   * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   * SOFTWARE.
   */
  var isBrowser =
    typeof window !== 'undefined' && typeof document !== 'undefined'

  var longerTimeoutBrowsers = ['Edge', 'Trident', 'Firefox']
  var timeoutDuration = 0
  for (var i = 0; i < longerTimeoutBrowsers.length; i += 1) {
    if (
      isBrowser &&
      navigator.userAgent.indexOf(longerTimeoutBrowsers[i]) >= 0
    ) {
      timeoutDuration = 1
      break
    }
  }

  function microtaskDebounce(fn) {
    var called = false
    return function() {
      if (called) {
        return
      }
      called = true
      window.Promise.resolve().then(function() {
        called = false
        fn()
      })
    }
  }

  function taskDebounce(fn) {
    var scheduled = false
    return function() {
      if (!scheduled) {
        scheduled = true
        setTimeout(function() {
          scheduled = false
          fn()
        }, timeoutDuration)
      }
    }
  }

  var supportsMicroTasks = isBrowser && window.Promise

  /**
   * Create a debounced version of a method, that's asynchronously deferred
   * but called in the minimum time possible.
   *
   * @method
   * @memberof Popper.Utils
   * @argument {Function} fn
   * @returns {Function}
   */
  var debounce$1 = supportsMicroTasks ? microtaskDebounce : taskDebounce

  /**
   * Check if the given variable is a function
   * @method
   * @memberof Popper.Utils
   * @argument {Any} functionToCheck - variable to check
   * @returns {Boolean} answer to: is a function?
   */
  function isFunction$1(functionToCheck) {
    var getType = {}
    return (
      functionToCheck &&
      getType.toString.call(functionToCheck) === '[object Function]'
    )
  }

  /**
   * Get CSS computed property of the given element
   * @method
   * @memberof Popper.Utils
   * @argument {Eement} element
   * @argument {String} property
   */
  function getStyleComputedProperty(element, property) {
    if (element.nodeType !== 1) {
      return []
    }
    // NOTE: 1 DOM access here
    var window = element.ownerDocument.defaultView
    var css = window.getComputedStyle(element, null)
    return property ? css[property] : css
  }

  /**
   * Returns the parentNode or the host of the element
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @returns {Element} parent
   */
  function getParentNode(element) {
    if (element.nodeName === 'HTML') {
      return element
    }
    return element.parentNode || element.host
  }

  /**
   * Returns the scrolling parent of the given element
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @returns {Element} scroll parent
   */
  function getScrollParent(element) {
    // Return body, `getScroll` will take care to get the correct `scrollTop` from it
    if (!element) {
      return document.body
    }

    switch (element.nodeName) {
      case 'HTML':
      case 'BODY':
        return element.ownerDocument.body
      case '#document':
        return element.body
    }

    // Firefox want us to check `-x` and `-y` variations as well

    var _getStyleComputedProp = getStyleComputedProperty(element),
      overflow = _getStyleComputedProp.overflow,
      overflowX = _getStyleComputedProp.overflowX,
      overflowY = _getStyleComputedProp.overflowY

    if (/(auto|scroll|overlay)/.test(overflow + overflowY + overflowX)) {
      return element
    }

    return getScrollParent(getParentNode(element))
  }

  var isIE11 =
    isBrowser && !!(window.MSInputMethodContext && document.documentMode)
  var isIE10 = isBrowser && /MSIE 10/.test(navigator.userAgent)

  /**
   * Determines if the browser is Internet Explorer
   * @method
   * @memberof Popper.Utils
   * @param {Number} version to check
   * @returns {Boolean} isIE
   */
  function isIE(version) {
    if (version === 11) {
      return isIE11
    }
    if (version === 10) {
      return isIE10
    }
    return isIE11 || isIE10
  }

  /**
   * Returns the offset parent of the given element
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @returns {Element} offset parent
   */
  function getOffsetParent(element) {
    if (!element) {
      return document.documentElement
    }

    var noOffsetParent = isIE(10) ? document.body : null

    // NOTE: 1 DOM access here
    var offsetParent = element.offsetParent || null
    // Skip hidden elements which don't have an offsetParent
    while (offsetParent === noOffsetParent && element.nextElementSibling) {
      offsetParent = (element = element.nextElementSibling).offsetParent
    }

    var nodeName = offsetParent && offsetParent.nodeName

    if (!nodeName || nodeName === 'BODY' || nodeName === 'HTML') {
      return element
        ? element.ownerDocument.documentElement
        : document.documentElement
    }

    // .offsetParent will return the closest TH, TD or TABLE in case
    // no offsetParent is present, I hate this job...
    if (
      ['TH', 'TD', 'TABLE'].indexOf(offsetParent.nodeName) !== -1 &&
      getStyleComputedProperty(offsetParent, 'position') === 'static'
    ) {
      return getOffsetParent(offsetParent)
    }

    return offsetParent
  }

  function isOffsetContainer(element) {
    var nodeName = element.nodeName

    if (nodeName === 'BODY') {
      return false
    }
    return (
      nodeName === 'HTML' ||
      getOffsetParent(element.firstElementChild) === element
    )
  }

  /**
   * Finds the root node (document, shadowDOM root) of the given element
   * @method
   * @memberof Popper.Utils
   * @argument {Element} node
   * @returns {Element} root node
   */
  function getRoot(node) {
    if (node.parentNode !== null) {
      return getRoot(node.parentNode)
    }

    return node
  }

  /**
   * Finds the offset parent common to the two provided nodes
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element1
   * @argument {Element} element2
   * @returns {Element} common offset parent
   */
  function findCommonOffsetParent(element1, element2) {
    // This check is needed to avoid errors in case one of the elements isn't defined for any reason
    if (!element1 || !element1.nodeType || !element2 || !element2.nodeType) {
      return document.documentElement
    }

    // Here we make sure to give as "start" the element that comes first in the DOM
    var order =
      element1.compareDocumentPosition(element2) &
      Node.DOCUMENT_POSITION_FOLLOWING
    var start = order ? element1 : element2
    var end = order ? element2 : element1

    // Get common ancestor container
    var range = document.createRange()
    range.setStart(start, 0)
    range.setEnd(end, 0)
    var commonAncestorContainer = range.commonAncestorContainer

    // Both nodes are inside #document

    if (
      (element1 !== commonAncestorContainer &&
        element2 !== commonAncestorContainer) ||
      start.contains(end)
    ) {
      if (isOffsetContainer(commonAncestorContainer)) {
        return commonAncestorContainer
      }

      return getOffsetParent(commonAncestorContainer)
    }

    // one of the nodes is inside shadowDOM, find which one
    var element1root = getRoot(element1)
    if (element1root.host) {
      return findCommonOffsetParent(element1root.host, element2)
    } else {
      return findCommonOffsetParent(element1, getRoot(element2).host)
    }
  }

  /**
   * Gets the scroll value of the given element in the given side (top and left)
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @argument {String} side `top` or `left`
   * @returns {number} amount of scrolled pixels
   */
  function getScroll(element) {
    var side =
      arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 'top'

    var upperSide = side === 'top' ? 'scrollTop' : 'scrollLeft'
    var nodeName = element.nodeName

    if (nodeName === 'BODY' || nodeName === 'HTML') {
      var html = element.ownerDocument.documentElement
      var scrollingElement = element.ownerDocument.scrollingElement || html
      return scrollingElement[upperSide]
    }

    return element[upperSide]
  }

  /*
   * Sum or subtract the element scroll values (left and top) from a given rect object
   * @method
   * @memberof Popper.Utils
   * @param {Object} rect - Rect object you want to change
   * @param {HTMLElement} element - The element from the function reads the scroll values
   * @param {Boolean} subtract - set to true if you want to subtract the scroll values
   * @return {Object} rect - The modifier rect object
   */
  function includeScroll(rect, element) {
    var subtract =
      arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : false

    var scrollTop = getScroll(element, 'top')
    var scrollLeft = getScroll(element, 'left')
    var modifier = subtract ? -1 : 1
    rect.top += scrollTop * modifier
    rect.bottom += scrollTop * modifier
    rect.left += scrollLeft * modifier
    rect.right += scrollLeft * modifier
    return rect
  }

  /*
   * Helper to detect borders of a given element
   * @method
   * @memberof Popper.Utils
   * @param {CSSStyleDeclaration} styles
   * Result of `getStyleComputedProperty` on the given element
   * @param {String} axis - `x` or `y`
   * @return {number} borders - The borders size of the given axis
   */

  function getBordersSize(styles, axis) {
    var sideA = axis === 'x' ? 'Left' : 'Top'
    var sideB = sideA === 'Left' ? 'Right' : 'Bottom'

    return (
      parseFloat(styles['border' + sideA + 'Width'], 10) +
      parseFloat(styles['border' + sideB + 'Width'], 10)
    )
  }

  function getSize(axis, body, html, computedStyle) {
    return Math.max(
      body['offset' + axis],
      body['scroll' + axis],
      html['client' + axis],
      html['offset' + axis],
      html['scroll' + axis],
      isIE(10)
        ? parseInt(html['offset' + axis]) +
            parseInt(
              computedStyle['margin' + (axis === 'Height' ? 'Top' : 'Left')]
            ) +
            parseInt(
              computedStyle['margin' + (axis === 'Height' ? 'Bottom' : 'Right')]
            )
        : 0
    )
  }

  function getWindowSizes(document) {
    var body = document.body
    var html = document.documentElement
    var computedStyle = isIE(10) && getComputedStyle(html)

    return {
      height: getSize('Height', body, html, computedStyle),
      width: getSize('Width', body, html, computedStyle),
    }
  }

  var classCallCheck = function(instance, Constructor) {
    if (!(instance instanceof Constructor)) {
      throw new TypeError('Cannot call a class as a function')
    }
  }

  var createClass = (function() {
    function defineProperties(target, props) {
      for (var i = 0; i < props.length; i++) {
        var descriptor = props[i]
        descriptor.enumerable = descriptor.enumerable || false
        descriptor.configurable = true
        if ('value' in descriptor) descriptor.writable = true
        Object.defineProperty(target, descriptor.key, descriptor)
      }
    }

    return function(Constructor, protoProps, staticProps) {
      if (protoProps) defineProperties(Constructor.prototype, protoProps)
      if (staticProps) defineProperties(Constructor, staticProps)
      return Constructor
    }
  })()

  var defineProperty$1 = function(obj, key, value) {
    if (key in obj) {
      Object.defineProperty(obj, key, {
        value: value,
        enumerable: true,
        configurable: true,
        writable: true,
      })
    } else {
      obj[key] = value
    }

    return obj
  }

  var _extends$1 =
    Object.assign ||
    function(target) {
      for (var i = 1; i < arguments.length; i++) {
        var source = arguments[i]

        for (var key in source) {
          if (Object.prototype.hasOwnProperty.call(source, key)) {
            target[key] = source[key]
          }
        }
      }

      return target
    }

  /**
   * Given element offsets, generate an output similar to getBoundingClientRect
   * @method
   * @memberof Popper.Utils
   * @argument {Object} offsets
   * @returns {Object} ClientRect like output
   */
  function getClientRect(offsets) {
    return _extends$1({}, offsets, {
      right: offsets.left + offsets.width,
      bottom: offsets.top + offsets.height,
    })
  }

  /**
   * Get bounding client rect of given element
   * @method
   * @memberof Popper.Utils
   * @param {HTMLElement} element
   * @return {Object} client rect
   */
  function getBoundingClientRect(element) {
    var rect = {}

    // IE10 10 FIX: Please, don't ask, the element isn't
    // considered in DOM in some circumstances...
    // This isn't reproducible in IE10 compatibility mode of IE11
    try {
      if (isIE(10)) {
        rect = element.getBoundingClientRect()
        var scrollTop = getScroll(element, 'top')
        var scrollLeft = getScroll(element, 'left')
        rect.top += scrollTop
        rect.left += scrollLeft
        rect.bottom += scrollTop
        rect.right += scrollLeft
      } else {
        rect = element.getBoundingClientRect()
      }
    } catch (e) {}

    var result = {
      left: rect.left,
      top: rect.top,
      width: rect.right - rect.left,
      height: rect.bottom - rect.top,
    }

    // subtract scrollbar size from sizes
    var sizes =
      element.nodeName === 'HTML' ? getWindowSizes(element.ownerDocument) : {}
    var width = sizes.width || element.clientWidth || result.right - result.left
    var height =
      sizes.height || element.clientHeight || result.bottom - result.top

    var horizScrollbar = element.offsetWidth - width
    var vertScrollbar = element.offsetHeight - height

    // if an hypothetical scrollbar is detected, we must be sure it's not a `border`
    // we make this check conditional for performance reasons
    if (horizScrollbar || vertScrollbar) {
      var styles = getStyleComputedProperty(element)
      horizScrollbar -= getBordersSize(styles, 'x')
      vertScrollbar -= getBordersSize(styles, 'y')

      result.width -= horizScrollbar
      result.height -= vertScrollbar
    }

    return getClientRect(result)
  }

  function getOffsetRectRelativeToArbitraryNode(children, parent) {
    var fixedPosition =
      arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : false

    var isIE10 = isIE(10)
    var isHTML = parent.nodeName === 'HTML'
    var childrenRect = getBoundingClientRect(children)
    var parentRect = getBoundingClientRect(parent)
    var scrollParent = getScrollParent(children)

    var styles = getStyleComputedProperty(parent)
    var borderTopWidth = parseFloat(styles.borderTopWidth, 10)
    var borderLeftWidth = parseFloat(styles.borderLeftWidth, 10)

    // In cases where the parent is fixed, we must ignore negative scroll in offset calc
    if (fixedPosition && isHTML) {
      parentRect.top = Math.max(parentRect.top, 0)
      parentRect.left = Math.max(parentRect.left, 0)
    }
    var offsets = getClientRect({
      top: childrenRect.top - parentRect.top - borderTopWidth,
      left: childrenRect.left - parentRect.left - borderLeftWidth,
      width: childrenRect.width,
      height: childrenRect.height,
    })
    offsets.marginTop = 0
    offsets.marginLeft = 0

    // Subtract margins of documentElement in case it's being used as parent
    // we do this only on HTML because it's the only element that behaves
    // differently when margins are applied to it. The margins are included in
    // the box of the documentElement, in the other cases not.
    if (!isIE10 && isHTML) {
      var marginTop = parseFloat(styles.marginTop, 10)
      var marginLeft = parseFloat(styles.marginLeft, 10)

      offsets.top -= borderTopWidth - marginTop
      offsets.bottom -= borderTopWidth - marginTop
      offsets.left -= borderLeftWidth - marginLeft
      offsets.right -= borderLeftWidth - marginLeft

      // Attach marginTop and marginLeft because in some circumstances we may need them
      offsets.marginTop = marginTop
      offsets.marginLeft = marginLeft
    }

    if (
      isIE10 && !fixedPosition
        ? parent.contains(scrollParent)
        : parent === scrollParent && scrollParent.nodeName !== 'BODY'
    ) {
      offsets = includeScroll(offsets, parent)
    }

    return offsets
  }

  function getViewportOffsetRectRelativeToArtbitraryNode(element) {
    var excludeScroll =
      arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : false

    var html = element.ownerDocument.documentElement
    var relativeOffset = getOffsetRectRelativeToArbitraryNode(element, html)
    var width = Math.max(html.clientWidth, window.innerWidth || 0)
    var height = Math.max(html.clientHeight, window.innerHeight || 0)

    var scrollTop = !excludeScroll ? getScroll(html) : 0
    var scrollLeft = !excludeScroll ? getScroll(html, 'left') : 0

    var offset = {
      top: scrollTop - relativeOffset.top + relativeOffset.marginTop,
      left: scrollLeft - relativeOffset.left + relativeOffset.marginLeft,
      width: width,
      height: height,
    }

    return getClientRect(offset)
  }

  /**
   * Check if the given element is fixed or is inside a fixed parent
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @argument {Element} customContainer
   * @returns {Boolean} answer to "isFixed?"
   */
  function isFixed(element) {
    var nodeName = element.nodeName
    if (nodeName === 'BODY' || nodeName === 'HTML') {
      return false
    }
    if (getStyleComputedProperty(element, 'position') === 'fixed') {
      return true
    }
    var parentNode = getParentNode(element)
    if (!parentNode) {
      return false
    }
    return isFixed(parentNode)
  }

  /**
   * Finds the first parent of an element that has a transformed property defined
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @returns {Element} first transformed parent or documentElement
   */

  function getFixedPositionOffsetParent(element) {
    // This check is needed to avoid errors in case one of the elements isn't defined for any reason
    if (!element || !element.parentElement || isIE()) {
      return document.documentElement
    }
    var el = element.parentElement
    while (el && getStyleComputedProperty(el, 'transform') === 'none') {
      el = el.parentElement
    }
    return el || document.documentElement
  }

  /**
   * Computed the boundaries limits and return them
   * @method
   * @memberof Popper.Utils
   * @param {HTMLElement} popper
   * @param {HTMLElement} reference
   * @param {number} padding
   * @param {HTMLElement} boundariesElement - Element used to define the boundaries
   * @param {Boolean} fixedPosition - Is in fixed position mode
   * @returns {Object} Coordinates of the boundaries
   */
  function getBoundaries(popper, reference, padding, boundariesElement) {
    var fixedPosition =
      arguments.length > 4 && arguments[4] !== undefined ? arguments[4] : false

    // NOTE: 1 DOM access here

    var boundaries = { top: 0, left: 0 }
    var offsetParent = fixedPosition
      ? getFixedPositionOffsetParent(popper)
      : findCommonOffsetParent(popper, reference)

    // Handle viewport case
    if (boundariesElement === 'viewport') {
      boundaries = getViewportOffsetRectRelativeToArtbitraryNode(
        offsetParent,
        fixedPosition
      )
    } else {
      // Handle other cases based on DOM element used as boundaries
      var boundariesNode = void 0
      if (boundariesElement === 'scrollParent') {
        boundariesNode = getScrollParent(getParentNode(reference))
        if (boundariesNode.nodeName === 'BODY') {
          boundariesNode = popper.ownerDocument.documentElement
        }
      } else if (boundariesElement === 'window') {
        boundariesNode = popper.ownerDocument.documentElement
      } else {
        boundariesNode = boundariesElement
      }

      var offsets = getOffsetRectRelativeToArbitraryNode(
        boundariesNode,
        offsetParent,
        fixedPosition
      )

      // In case of HTML, we need a different computation
      if (boundariesNode.nodeName === 'HTML' && !isFixed(offsetParent)) {
        var _getWindowSizes = getWindowSizes(popper.ownerDocument),
          height = _getWindowSizes.height,
          width = _getWindowSizes.width

        boundaries.top += offsets.top - offsets.marginTop
        boundaries.bottom = height + offsets.top
        boundaries.left += offsets.left - offsets.marginLeft
        boundaries.right = width + offsets.left
      } else {
        // for all the other DOM elements, this one is good
        boundaries = offsets
      }
    }

    // Add paddings
    padding = padding || 0
    var isPaddingNumber = typeof padding === 'number'
    boundaries.left += isPaddingNumber ? padding : padding.left || 0
    boundaries.top += isPaddingNumber ? padding : padding.top || 0
    boundaries.right -= isPaddingNumber ? padding : padding.right || 0
    boundaries.bottom -= isPaddingNumber ? padding : padding.bottom || 0

    return boundaries
  }

  function getArea(_ref) {
    var width = _ref.width,
      height = _ref.height

    return width * height
  }

  /**
   * Utility used to transform the `auto` placement to the placement with more
   * available space.
   * @method
   * @memberof Popper.Utils
   * @argument {Object} data - The data object generated by update method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function computeAutoPlacement(
    placement,
    refRect,
    popper,
    reference,
    boundariesElement
  ) {
    var padding =
      arguments.length > 5 && arguments[5] !== undefined ? arguments[5] : 0

    if (placement.indexOf('auto') === -1) {
      return placement
    }

    var boundaries = getBoundaries(
      popper,
      reference,
      padding,
      boundariesElement
    )

    var rects = {
      top: {
        width: boundaries.width,
        height: refRect.top - boundaries.top,
      },
      right: {
        width: boundaries.right - refRect.right,
        height: boundaries.height,
      },
      bottom: {
        width: boundaries.width,
        height: boundaries.bottom - refRect.bottom,
      },
      left: {
        width: refRect.left - boundaries.left,
        height: boundaries.height,
      },
    }

    var sortedAreas = Object.keys(rects)
      .map(function(key) {
        return _extends$1(
          {
            key: key,
          },
          rects[key],
          {
            area: getArea(rects[key]),
          }
        )
      })
      .sort(function(a, b) {
        return b.area - a.area
      })

    var filteredAreas = sortedAreas.filter(function(_ref2) {
      var width = _ref2.width,
        height = _ref2.height
      return width >= popper.clientWidth && height >= popper.clientHeight
    })

    var computedPlacement =
      filteredAreas.length > 0 ? filteredAreas[0].key : sortedAreas[0].key

    var variation = placement.split('-')[1]

    return computedPlacement + (variation ? '-' + variation : '')
  }

  /**
   * Get offsets to the reference element
   * @method
   * @memberof Popper.Utils
   * @param {Object} state
   * @param {Element} popper - the popper element
   * @param {Element} reference - the reference element (the popper will be relative to this)
   * @param {Element} fixedPosition - is in fixed position mode
   * @returns {Object} An object containing the offsets which will be applied to the popper
   */
  function getReferenceOffsets(state, popper, reference) {
    var fixedPosition =
      arguments.length > 3 && arguments[3] !== undefined ? arguments[3] : null

    var commonOffsetParent = fixedPosition
      ? getFixedPositionOffsetParent(popper)
      : findCommonOffsetParent(popper, reference)
    return getOffsetRectRelativeToArbitraryNode(
      reference,
      commonOffsetParent,
      fixedPosition
    )
  }

  /**
   * Get the outer sizes of the given element (offset size + margins)
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element
   * @returns {Object} object containing width and height properties
   */
  function getOuterSizes(element) {
    var window = element.ownerDocument.defaultView
    var styles = window.getComputedStyle(element)
    var x =
      parseFloat(styles.marginTop || 0) + parseFloat(styles.marginBottom || 0)
    var y =
      parseFloat(styles.marginLeft || 0) + parseFloat(styles.marginRight || 0)
    var result = {
      width: element.offsetWidth + y,
      height: element.offsetHeight + x,
    }
    return result
  }

  /**
   * Get the opposite placement of the given one
   * @method
   * @memberof Popper.Utils
   * @argument {String} placement
   * @returns {String} flipped placement
   */
  function getOppositePlacement(placement) {
    var hash = { left: 'right', right: 'left', bottom: 'top', top: 'bottom' }
    return placement.replace(/left|right|bottom|top/g, function(matched) {
      return hash[matched]
    })
  }

  /**
   * Get offsets to the popper
   * @method
   * @memberof Popper.Utils
   * @param {Object} position - CSS position the Popper will get applied
   * @param {HTMLElement} popper - the popper element
   * @param {Object} referenceOffsets - the reference offsets (the popper will be relative to this)
   * @param {String} placement - one of the valid placement options
   * @returns {Object} popperOffsets - An object containing the offsets which will be applied to the popper
   */
  function getPopperOffsets(popper, referenceOffsets, placement) {
    placement = placement.split('-')[0]

    // Get popper node sizes
    var popperRect = getOuterSizes(popper)

    // Add position, width and height to our offsets object
    var popperOffsets = {
      width: popperRect.width,
      height: popperRect.height,
    }

    // depending by the popper placement we have to compute its offsets slightly differently
    var isHoriz = ['right', 'left'].indexOf(placement) !== -1
    var mainSide = isHoriz ? 'top' : 'left'
    var secondarySide = isHoriz ? 'left' : 'top'
    var measurement = isHoriz ? 'height' : 'width'
    var secondaryMeasurement = !isHoriz ? 'height' : 'width'

    popperOffsets[mainSide] =
      referenceOffsets[mainSide] +
      referenceOffsets[measurement] / 2 -
      popperRect[measurement] / 2
    if (placement === secondarySide) {
      popperOffsets[secondarySide] =
        referenceOffsets[secondarySide] - popperRect[secondaryMeasurement]
    } else {
      popperOffsets[secondarySide] =
        referenceOffsets[getOppositePlacement(secondarySide)]
    }

    return popperOffsets
  }

  /**
   * Mimics the `find` method of Array
   * @method
   * @memberof Popper.Utils
   * @argument {Array} arr
   * @argument prop
   * @argument value
   * @returns index or -1
   */
  function find$1(arr, check) {
    // use native find if supported
    if (Array.prototype.find) {
      return arr.find(check)
    }

    // use `filter` to obtain the same behavior of `find`
    return arr.filter(check)[0]
  }

  /**
   * Return the index of the matching object
   * @method
   * @memberof Popper.Utils
   * @argument {Array} arr
   * @argument prop
   * @argument value
   * @returns index or -1
   */
  function findIndex$1(arr, prop, value) {
    // use native findIndex if supported
    if (Array.prototype.findIndex) {
      return arr.findIndex(function(cur) {
        return cur[prop] === value
      })
    }

    // use `find` + `indexOf` if `findIndex` isn't supported
    var match = find$1(arr, function(obj) {
      return obj[prop] === value
    })
    return arr.indexOf(match)
  }

  /**
   * Loop trough the list of modifiers and run them in order,
   * each of them will then edit the data object.
   * @method
   * @memberof Popper.Utils
   * @param {dataObject} data
   * @param {Array} modifiers
   * @param {String} ends - Optional modifier name used as stopper
   * @returns {dataObject}
   */
  function runModifiers(modifiers, data, ends) {
    var modifiersToRun =
      ends === undefined
        ? modifiers
        : modifiers.slice(0, findIndex$1(modifiers, 'name', ends))

    modifiersToRun.forEach(function(modifier) {
      if (modifier['function']) {
        // eslint-disable-line dot-notation
        console.warn('`modifier.function` is deprecated, use `modifier.fn`!')
      }
      var fn = modifier['function'] || modifier.fn // eslint-disable-line dot-notation
      if (modifier.enabled && isFunction$1(fn)) {
        // Add properties to offsets to make them a complete clientRect object
        // we do this before each modifier to make sure the previous one doesn't
        // mess with these values
        data.offsets.popper = getClientRect(data.offsets.popper)
        data.offsets.reference = getClientRect(data.offsets.reference)

        data = fn(data, modifier)
      }
    })

    return data
  }

  /**
   * Updates the position of the popper, computing the new offsets and applying
   * the new style.<br />
   * Prefer `scheduleUpdate` over `update` because of performance reasons.
   * @method
   * @memberof Popper
   */
  function update$1() {
    // if popper is destroyed, don't perform any further update
    if (this.state.isDestroyed) {
      return
    }

    var data = {
      instance: this,
      styles: {},
      arrowStyles: {},
      attributes: {},
      flipped: false,
      offsets: {},
    }

    // compute reference element offsets
    data.offsets.reference = getReferenceOffsets(
      this.state,
      this.popper,
      this.reference,
      this.options.positionFixed
    )

    // compute auto placement, store placement inside the data object,
    // modifiers will be able to edit `placement` if needed
    // and refer to originalPlacement to know the original value
    data.placement = computeAutoPlacement(
      this.options.placement,
      data.offsets.reference,
      this.popper,
      this.reference,
      this.options.modifiers.flip.boundariesElement,
      this.options.modifiers.flip.padding
    )

    // store the computed placement inside `originalPlacement`
    data.originalPlacement = data.placement

    data.positionFixed = this.options.positionFixed

    // compute the popper offsets
    data.offsets.popper = getPopperOffsets(
      this.popper,
      data.offsets.reference,
      data.placement
    )

    data.offsets.popper.position = this.options.positionFixed
      ? 'fixed'
      : 'absolute'

    // run the modifiers
    data = runModifiers(this.modifiers, data)

    // the first `update` will call `onCreate` callback
    // the other ones will call `onUpdate` callback
    if (!this.state.isCreated) {
      this.state.isCreated = true
      this.options.onCreate(data)
    } else {
      this.options.onUpdate(data)
    }
  }

  /**
   * Helper used to know if the given modifier is enabled.
   * @method
   * @memberof Popper.Utils
   * @returns {Boolean}
   */
  function isModifierEnabled(modifiers, modifierName) {
    return modifiers.some(function(_ref) {
      var name = _ref.name,
        enabled = _ref.enabled
      return enabled && name === modifierName
    })
  }

  /**
   * Get the prefixed supported property name
   * @method
   * @memberof Popper.Utils
   * @argument {String} property (camelCase)
   * @returns {String} prefixed property (camelCase or PascalCase, depending on the vendor prefix)
   */
  function getSupportedPropertyName(property) {
    var prefixes = [false, 'ms', 'Webkit', 'Moz', 'O']
    var upperProp = property.charAt(0).toUpperCase() + property.slice(1)

    for (var i = 0; i < prefixes.length; i++) {
      var prefix = prefixes[i]
      var toCheck = prefix ? '' + prefix + upperProp : property
      if (typeof document.body.style[toCheck] !== 'undefined') {
        return toCheck
      }
    }
    return null
  }

  /**
   * Destroys the popper.
   * @method
   * @memberof Popper
   */
  function destroy() {
    this.state.isDestroyed = true

    // touch DOM only if `applyStyle` modifier is enabled
    if (isModifierEnabled(this.modifiers, 'applyStyle')) {
      this.popper.removeAttribute('x-placement')
      this.popper.style.position = ''
      this.popper.style.top = ''
      this.popper.style.left = ''
      this.popper.style.right = ''
      this.popper.style.bottom = ''
      this.popper.style.willChange = ''
      this.popper.style[getSupportedPropertyName('transform')] = ''
    }

    this.disableEventListeners()

    // remove the popper if user explicity asked for the deletion on destroy
    // do not use `remove` because IE11 doesn't support it
    if (this.options.removeOnDestroy) {
      this.popper.parentNode.removeChild(this.popper)
    }
    return this
  }

  /**
   * Get the window associated with the element
   * @argument {Element} element
   * @returns {Window}
   */
  function getWindow(element) {
    var ownerDocument = element.ownerDocument
    return ownerDocument ? ownerDocument.defaultView : window
  }

  function attachToScrollParents(scrollParent, event, callback, scrollParents) {
    var isBody = scrollParent.nodeName === 'BODY'
    var target = isBody ? scrollParent.ownerDocument.defaultView : scrollParent
    target.addEventListener(event, callback, { passive: true })

    if (!isBody) {
      attachToScrollParents(
        getScrollParent(target.parentNode),
        event,
        callback,
        scrollParents
      )
    }
    scrollParents.push(target)
  }

  /**
   * Setup needed event listeners used to update the popper position
   * @method
   * @memberof Popper.Utils
   * @private
   */
  function setupEventListeners(reference, options, state, updateBound) {
    // Resize event listener on window
    state.updateBound = updateBound
    getWindow(reference).addEventListener('resize', state.updateBound, {
      passive: true,
    })

    // Scroll event listener on scroll parents
    var scrollElement = getScrollParent(reference)
    attachToScrollParents(
      scrollElement,
      'scroll',
      state.updateBound,
      state.scrollParents
    )
    state.scrollElement = scrollElement
    state.eventsEnabled = true

    return state
  }

  /**
   * It will add resize/scroll events and start recalculating
   * position of the popper element when they are triggered.
   * @method
   * @memberof Popper
   */
  function enableEventListeners() {
    if (!this.state.eventsEnabled) {
      this.state = setupEventListeners(
        this.reference,
        this.options,
        this.state,
        this.scheduleUpdate
      )
    }
  }

  /**
   * Remove event listeners used to update the popper position
   * @method
   * @memberof Popper.Utils
   * @private
   */
  function removeEventListeners(reference, state) {
    // Remove resize event listener on window
    getWindow(reference).removeEventListener('resize', state.updateBound)

    // Remove scroll event listener on scroll parents
    state.scrollParents.forEach(function(target) {
      target.removeEventListener('scroll', state.updateBound)
    })

    // Reset state
    state.updateBound = null
    state.scrollParents = []
    state.scrollElement = null
    state.eventsEnabled = false
    return state
  }

  /**
   * It will remove resize/scroll events and won't recalculate popper position
   * when they are triggered. It also won't trigger `onUpdate` callback anymore,
   * unless you call `update` method manually.
   * @method
   * @memberof Popper
   */
  function disableEventListeners() {
    if (this.state.eventsEnabled) {
      cancelAnimationFrame(this.scheduleUpdate)
      this.state = removeEventListeners(this.reference, this.state)
    }
  }

  /**
   * Tells if a given input is a number
   * @method
   * @memberof Popper.Utils
   * @param {*} input to check
   * @return {Boolean}
   */
  function isNumeric(n) {
    return n !== '' && !isNaN(parseFloat(n)) && isFinite(n)
  }

  /**
   * Set the style to the given popper
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element - Element to apply the style to
   * @argument {Object} styles
   * Object with a list of properties and values which will be applied to the element
   */
  function setStyles(element, styles) {
    Object.keys(styles).forEach(function(prop) {
      var unit = ''
      // add unit if the value is numeric and is one of the following
      if (
        ['width', 'height', 'top', 'right', 'bottom', 'left'].indexOf(prop) !==
          -1 &&
        isNumeric(styles[prop])
      ) {
        unit = 'px'
      }
      element.style[prop] = styles[prop] + unit
    })
  }

  /**
   * Set the attributes to the given popper
   * @method
   * @memberof Popper.Utils
   * @argument {Element} element - Element to apply the attributes to
   * @argument {Object} styles
   * Object with a list of properties and values which will be applied to the element
   */
  function setAttributes(element, attributes) {
    Object.keys(attributes).forEach(function(prop) {
      var value = attributes[prop]
      if (value !== false) {
        element.setAttribute(prop, attributes[prop])
      } else {
        element.removeAttribute(prop)
      }
    })
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by `update` method
   * @argument {Object} data.styles - List of style properties - values to apply to popper element
   * @argument {Object} data.attributes - List of attribute properties - values to apply to popper element
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The same data object
   */
  function applyStyle(data) {
    // any property present in `data.styles` will be applied to the popper,
    // in this way we can make the 3rd party modifiers add custom styles to it
    // Be aware, modifiers could override the properties defined in the previous
    // lines of this modifier!
    setStyles(data.instance.popper, data.styles)

    // any property present in `data.attributes` will be applied to the popper,
    // they will be set as HTML attributes of the element
    setAttributes(data.instance.popper, data.attributes)

    // if arrowElement is defined and arrowStyles has some properties
    if (data.arrowElement && Object.keys(data.arrowStyles).length) {
      setStyles(data.arrowElement, data.arrowStyles)
    }

    return data
  }

  /**
   * Set the x-placement attribute before everything else because it could be used
   * to add margins to the popper margins needs to be calculated to get the
   * correct popper offsets.
   * @method
   * @memberof Popper.modifiers
   * @param {HTMLElement} reference - The reference element used to position the popper
   * @param {HTMLElement} popper - The HTML element used as popper
   * @param {Object} options - Popper.js options
   */
  function applyStyleOnLoad(
    reference,
    popper,
    options,
    modifierOptions,
    state
  ) {
    // compute reference element offsets
    var referenceOffsets = getReferenceOffsets(
      state,
      popper,
      reference,
      options.positionFixed
    )

    // compute auto placement, store placement inside the data object,
    // modifiers will be able to edit `placement` if needed
    // and refer to originalPlacement to know the original value
    var placement = computeAutoPlacement(
      options.placement,
      referenceOffsets,
      popper,
      reference,
      options.modifiers.flip.boundariesElement,
      options.modifiers.flip.padding
    )

    popper.setAttribute('x-placement', placement)

    // Apply `position` to popper before anything else because
    // without the position applied we can't guarantee correct computations
    setStyles(popper, {
      position: options.positionFixed ? 'fixed' : 'absolute',
    })

    return options
  }

  /**
   * @function
   * @memberof Popper.Utils
   * @argument {Object} data - The data object generated by `update` method
   * @argument {Boolean} shouldRound - If the offsets should be rounded at all
   * @returns {Object} The popper's position offsets rounded
   *
   * The tale of pixel-perfect positioning. It's still not 100% perfect, but as
   * good as it can be within reason.
   * Discussion here: https://github.com/FezVrasta/popper.js/pull/715
   *
   * Low DPI screens cause a popper to be blurry if not using full pixels (Safari
   * as well on High DPI screens).
   *
   * Firefox prefers no rounding for positioning and does not have blurriness on
   * high DPI screens.
   *
   * Only horizontal placement and left/right values need to be considered.
   */
  function getRoundedOffsets(data, shouldRound) {
    var _data$offsets = data.offsets,
      popper = _data$offsets.popper,
      reference = _data$offsets.reference
    var round = Math.round,
      floor = Math.floor

    var noRound = function noRound(v) {
      return v
    }

    var referenceWidth = round(reference.width)
    var popperWidth = round(popper.width)

    var isVertical = ['left', 'right'].indexOf(data.placement) !== -1
    var isVariation = data.placement.indexOf('-') !== -1
    var sameWidthParity = referenceWidth % 2 === popperWidth % 2
    var bothOddWidth = referenceWidth % 2 === 1 && popperWidth % 2 === 1

    var horizontalToInteger = !shouldRound
      ? noRound
      : isVertical || isVariation || sameWidthParity
      ? round
      : floor
    var verticalToInteger = !shouldRound ? noRound : round

    return {
      left: horizontalToInteger(
        bothOddWidth && !isVariation && shouldRound
          ? popper.left - 1
          : popper.left
      ),
      top: verticalToInteger(popper.top),
      bottom: verticalToInteger(popper.bottom),
      right: horizontalToInteger(popper.right),
    }
  }

  var isFirefox = isBrowser && /Firefox/i.test(navigator.userAgent)

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by `update` method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function computeStyle(data, options) {
    var x = options.x,
      y = options.y
    var popper = data.offsets.popper

    // Remove this legacy support in Popper.js v2

    var legacyGpuAccelerationOption = find$1(data.instance.modifiers, function(
      modifier
    ) {
      return modifier.name === 'applyStyle'
    }).gpuAcceleration
    if (legacyGpuAccelerationOption !== undefined) {
      console.warn(
        'WARNING: `gpuAcceleration` option moved to `computeStyle` modifier and will not be supported in future versions of Popper.js!'
      )
    }
    var gpuAcceleration =
      legacyGpuAccelerationOption !== undefined
        ? legacyGpuAccelerationOption
        : options.gpuAcceleration

    var offsetParent = getOffsetParent(data.instance.popper)
    var offsetParentRect = getBoundingClientRect(offsetParent)

    // Styles
    var styles = {
      position: popper.position,
    }

    var offsets = getRoundedOffsets(
      data,
      window.devicePixelRatio < 2 || !isFirefox
    )

    var sideA = x === 'bottom' ? 'top' : 'bottom'
    var sideB = y === 'right' ? 'left' : 'right'

    // if gpuAcceleration is set to `true` and transform is supported,
    //  we use `translate3d` to apply the position to the popper we
    // automatically use the supported prefixed version if needed
    var prefixedProperty = getSupportedPropertyName('transform')

    // now, let's make a step back and look at this code closely (wtf?)
    // If the content of the popper grows once it's been positioned, it
    // may happen that the popper gets misplaced because of the new content
    // overflowing its reference element
    // To avoid this problem, we provide two options (x and y), which allow
    // the consumer to define the offset origin.
    // If we position a popper on top of a reference element, we can set
    // `x` to `top` to make the popper grow towards its top instead of
    // its bottom.
    var left = void 0,
      top = void 0
    if (sideA === 'bottom') {
      // when offsetParent is <html> the positioning is relative to the bottom of the screen (excluding the scrollbar)
      // and not the bottom of the html element
      if (offsetParent.nodeName === 'HTML') {
        top = -offsetParent.clientHeight + offsets.bottom
      } else {
        top = -offsetParentRect.height + offsets.bottom
      }
    } else {
      top = offsets.top
    }
    if (sideB === 'right') {
      if (offsetParent.nodeName === 'HTML') {
        left = -offsetParent.clientWidth + offsets.right
      } else {
        left = -offsetParentRect.width + offsets.right
      }
    } else {
      left = offsets.left
    }
    if (gpuAcceleration && prefixedProperty) {
      styles[prefixedProperty] = 'translate3d(' + left + 'px, ' + top + 'px, 0)'
      styles[sideA] = 0
      styles[sideB] = 0
      styles.willChange = 'transform'
    } else {
      // othwerise, we use the standard `top`, `left`, `bottom` and `right` properties
      var invertTop = sideA === 'bottom' ? -1 : 1
      var invertLeft = sideB === 'right' ? -1 : 1
      styles[sideA] = top * invertTop
      styles[sideB] = left * invertLeft
      styles.willChange = sideA + ', ' + sideB
    }

    // Attributes
    var attributes = {
      'x-placement': data.placement,
    }

    // Update `data` attributes, styles and arrowStyles
    data.attributes = _extends$1({}, attributes, data.attributes)
    data.styles = _extends$1({}, styles, data.styles)
    data.arrowStyles = _extends$1({}, data.offsets.arrow, data.arrowStyles)

    return data
  }

  /**
   * Helper used to know if the given modifier depends from another one.<br />
   * It checks if the needed modifier is listed and enabled.
   * @method
   * @memberof Popper.Utils
   * @param {Array} modifiers - list of modifiers
   * @param {String} requestingName - name of requesting modifier
   * @param {String} requestedName - name of requested modifier
   * @returns {Boolean}
   */
  function isModifierRequired(modifiers, requestingName, requestedName) {
    var requesting = find$1(modifiers, function(_ref) {
      var name = _ref.name
      return name === requestingName
    })

    var isRequired =
      !!requesting &&
      modifiers.some(function(modifier) {
        return (
          modifier.name === requestedName &&
          modifier.enabled &&
          modifier.order < requesting.order
        )
      })

    if (!isRequired) {
      var _requesting = '`' + requestingName + '`'
      var requested = '`' + requestedName + '`'
      console.warn(
        requested +
          ' modifier is required by ' +
          _requesting +
          ' modifier in order to work, be sure to include it before ' +
          _requesting +
          '!'
      )
    }
    return isRequired
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by update method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function arrow(data, options) {
    var _data$offsets$arrow

    // arrow depends on keepTogether in order to work
    if (!isModifierRequired(data.instance.modifiers, 'arrow', 'keepTogether')) {
      return data
    }

    var arrowElement = options.element

    // if arrowElement is a string, suppose it's a CSS selector
    if (typeof arrowElement === 'string') {
      arrowElement = data.instance.popper.querySelector(arrowElement)

      // if arrowElement is not found, don't run the modifier
      if (!arrowElement) {
        return data
      }
    } else {
      // if the arrowElement isn't a query selector we must check that the
      // provided DOM node is child of its popper node
      if (!data.instance.popper.contains(arrowElement)) {
        console.warn(
          'WARNING: `arrow.element` must be child of its popper element!'
        )
        return data
      }
    }

    var placement = data.placement.split('-')[0]
    var _data$offsets = data.offsets,
      popper = _data$offsets.popper,
      reference = _data$offsets.reference

    var isVertical = ['left', 'right'].indexOf(placement) !== -1

    var len = isVertical ? 'height' : 'width'
    var sideCapitalized = isVertical ? 'Top' : 'Left'
    var side = sideCapitalized.toLowerCase()
    var altSide = isVertical ? 'left' : 'top'
    var opSide = isVertical ? 'bottom' : 'right'
    var arrowElementSize = getOuterSizes(arrowElement)[len]

    //
    // extends keepTogether behavior making sure the popper and its
    // reference have enough pixels in conjunction
    //

    // top/left side
    if (reference[opSide] - arrowElementSize < popper[side]) {
      data.offsets.popper[side] -=
        popper[side] - (reference[opSide] - arrowElementSize)
    }
    // bottom/right side
    if (reference[side] + arrowElementSize > popper[opSide]) {
      data.offsets.popper[side] +=
        reference[side] + arrowElementSize - popper[opSide]
    }
    data.offsets.popper = getClientRect(data.offsets.popper)

    // compute center of the popper
    var center = reference[side] + reference[len] / 2 - arrowElementSize / 2

    // Compute the sideValue using the updated popper offsets
    // take popper margin in account because we don't have this info available
    var css = getStyleComputedProperty(data.instance.popper)
    var popperMarginSide = parseFloat(css['margin' + sideCapitalized], 10)
    var popperBorderSide = parseFloat(
      css['border' + sideCapitalized + 'Width'],
      10
    )
    var sideValue =
      center - data.offsets.popper[side] - popperMarginSide - popperBorderSide

    // prevent arrowElement from being placed not contiguously to its popper
    sideValue = Math.max(Math.min(popper[len] - arrowElementSize, sideValue), 0)

    data.arrowElement = arrowElement
    data.offsets.arrow =
      ((_data$offsets$arrow = {}),
      defineProperty$1(_data$offsets$arrow, side, Math.round(sideValue)),
      defineProperty$1(_data$offsets$arrow, altSide, ''),
      _data$offsets$arrow)

    return data
  }

  /**
   * Get the opposite placement variation of the given one
   * @method
   * @memberof Popper.Utils
   * @argument {String} placement variation
   * @returns {String} flipped placement variation
   */
  function getOppositeVariation(variation) {
    if (variation === 'end') {
      return 'start'
    } else if (variation === 'start') {
      return 'end'
    }
    return variation
  }

  /**
   * List of accepted placements to use as values of the `placement` option.<br />
   * Valid placements are:
   * - `auto`
   * - `top`
   * - `right`
   * - `bottom`
   * - `left`
   *
   * Each placement can have a variation from this list:
   * - `-start`
   * - `-end`
   *
   * Variations are interpreted easily if you think of them as the left to right
   * written languages. Horizontally (`top` and `bottom`), `start` is left and `end`
   * is right.<br />
   * Vertically (`left` and `right`), `start` is top and `end` is bottom.
   *
   * Some valid examples are:
   * - `top-end` (on top of reference, right aligned)
   * - `right-start` (on right of reference, top aligned)
   * - `bottom` (on bottom, centered)
   * - `auto-end` (on the side with more space available, alignment depends by placement)
   *
   * @static
   * @type {Array}
   * @enum {String}
   * @readonly
   * @method placements
   * @memberof Popper
   */
  var placements = [
    'auto-start',
    'auto',
    'auto-end',
    'top-start',
    'top',
    'top-end',
    'right-start',
    'right',
    'right-end',
    'bottom-end',
    'bottom',
    'bottom-start',
    'left-end',
    'left',
    'left-start',
  ]

  // Get rid of `auto` `auto-start` and `auto-end`
  var validPlacements = placements.slice(3)

  /**
   * Given an initial placement, returns all the subsequent placements
   * clockwise (or counter-clockwise).
   *
   * @method
   * @memberof Popper.Utils
   * @argument {String} placement - A valid placement (it accepts variations)
   * @argument {Boolean} counter - Set to true to walk the placements counterclockwise
   * @returns {Array} placements including their variations
   */
  function clockwise(placement) {
    var counter =
      arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : false

    var index = validPlacements.indexOf(placement)
    var arr = validPlacements
      .slice(index + 1)
      .concat(validPlacements.slice(0, index))
    return counter ? arr.reverse() : arr
  }

  var BEHAVIORS = {
    FLIP: 'flip',
    CLOCKWISE: 'clockwise',
    COUNTERCLOCKWISE: 'counterclockwise',
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by update method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function flip$1(data, options) {
    // if `inner` modifier is enabled, we can't use the `flip` modifier
    if (isModifierEnabled(data.instance.modifiers, 'inner')) {
      return data
    }

    if (data.flipped && data.placement === data.originalPlacement) {
      // seems like flip is trying to loop, probably there's not enough space on any of the flippable sides
      return data
    }

    var boundaries = getBoundaries(
      data.instance.popper,
      data.instance.reference,
      options.padding,
      options.boundariesElement,
      data.positionFixed
    )

    var placement = data.placement.split('-')[0]
    var placementOpposite = getOppositePlacement(placement)
    var variation = data.placement.split('-')[1] || ''

    var flipOrder = []

    switch (options.behavior) {
      case BEHAVIORS.FLIP:
        flipOrder = [placement, placementOpposite]
        break
      case BEHAVIORS.CLOCKWISE:
        flipOrder = clockwise(placement)
        break
      case BEHAVIORS.COUNTERCLOCKWISE:
        flipOrder = clockwise(placement, true)
        break
      default:
        flipOrder = options.behavior
    }

    flipOrder.forEach(function(step, index) {
      if (placement !== step || flipOrder.length === index + 1) {
        return data
      }

      placement = data.placement.split('-')[0]
      placementOpposite = getOppositePlacement(placement)

      var popperOffsets = data.offsets.popper
      var refOffsets = data.offsets.reference

      // using floor because the reference offsets may contain decimals we are not going to consider here
      var floor = Math.floor
      var overlapsRef =
        (placement === 'left' &&
          floor(popperOffsets.right) > floor(refOffsets.left)) ||
        (placement === 'right' &&
          floor(popperOffsets.left) < floor(refOffsets.right)) ||
        (placement === 'top' &&
          floor(popperOffsets.bottom) > floor(refOffsets.top)) ||
        (placement === 'bottom' &&
          floor(popperOffsets.top) < floor(refOffsets.bottom))

      var overflowsLeft = floor(popperOffsets.left) < floor(boundaries.left)
      var overflowsRight = floor(popperOffsets.right) > floor(boundaries.right)
      var overflowsTop = floor(popperOffsets.top) < floor(boundaries.top)
      var overflowsBottom =
        floor(popperOffsets.bottom) > floor(boundaries.bottom)

      var overflowsBoundaries =
        (placement === 'left' && overflowsLeft) ||
        (placement === 'right' && overflowsRight) ||
        (placement === 'top' && overflowsTop) ||
        (placement === 'bottom' && overflowsBottom)

      // flip the variation if required
      var isVertical = ['top', 'bottom'].indexOf(placement) !== -1

      // flips variation if reference element overflows boundaries
      var flippedVariationByRef =
        !!options.flipVariations &&
        ((isVertical && variation === 'start' && overflowsLeft) ||
          (isVertical && variation === 'end' && overflowsRight) ||
          (!isVertical && variation === 'start' && overflowsTop) ||
          (!isVertical && variation === 'end' && overflowsBottom))

      // flips variation if popper content overflows boundaries
      var flippedVariationByContent =
        !!options.flipVariationsByContent &&
        ((isVertical && variation === 'start' && overflowsRight) ||
          (isVertical && variation === 'end' && overflowsLeft) ||
          (!isVertical && variation === 'start' && overflowsBottom) ||
          (!isVertical && variation === 'end' && overflowsTop))

      var flippedVariation = flippedVariationByRef || flippedVariationByContent

      if (overlapsRef || overflowsBoundaries || flippedVariation) {
        // this boolean to detect any flip loop
        data.flipped = true

        if (overlapsRef || overflowsBoundaries) {
          placement = flipOrder[index + 1]
        }

        if (flippedVariation) {
          variation = getOppositeVariation(variation)
        }

        data.placement = placement + (variation ? '-' + variation : '')

        // this object contains `position`, we want to preserve it along with
        // any additional property we may add in the future
        data.offsets.popper = _extends$1(
          {},
          data.offsets.popper,
          getPopperOffsets(
            data.instance.popper,
            data.offsets.reference,
            data.placement
          )
        )

        data = runModifiers(data.instance.modifiers, data, 'flip')
      }
    })
    return data
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by update method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function keepTogether(data) {
    var _data$offsets = data.offsets,
      popper = _data$offsets.popper,
      reference = _data$offsets.reference

    var placement = data.placement.split('-')[0]
    var floor = Math.floor
    var isVertical = ['top', 'bottom'].indexOf(placement) !== -1
    var side = isVertical ? 'right' : 'bottom'
    var opSide = isVertical ? 'left' : 'top'
    var measurement = isVertical ? 'width' : 'height'

    if (popper[side] < floor(reference[opSide])) {
      data.offsets.popper[opSide] =
        floor(reference[opSide]) - popper[measurement]
    }
    if (popper[opSide] > floor(reference[side])) {
      data.offsets.popper[opSide] = floor(reference[side])
    }

    return data
  }

  /**
   * Converts a string containing value + unit into a px value number
   * @function
   * @memberof {modifiers~offset}
   * @private
   * @argument {String} str - Value + unit string
   * @argument {String} measurement - `height` or `width`
   * @argument {Object} popperOffsets
   * @argument {Object} referenceOffsets
   * @returns {Number|String}
   * Value in pixels, or original string if no values were extracted
   */
  function toValue(str, measurement, popperOffsets, referenceOffsets) {
    // separate value from unit
    var split = str.match(/((?:\-|\+)?\d*\.?\d*)(.*)/)
    var value = +split[1]
    var unit = split[2]

    // If it's not a number it's an operator, I guess
    if (!value) {
      return str
    }

    if (unit.indexOf('%') === 0) {
      var element = void 0
      switch (unit) {
        case '%p':
          element = popperOffsets
          break
        case '%':
        case '%r':
        default:
          element = referenceOffsets
      }

      var rect = getClientRect(element)
      return (rect[measurement] / 100) * value
    } else if (unit === 'vh' || unit === 'vw') {
      // if is a vh or vw, we calculate the size based on the viewport
      var size = void 0
      if (unit === 'vh') {
        size = Math.max(
          document.documentElement.clientHeight,
          window.innerHeight || 0
        )
      } else {
        size = Math.max(
          document.documentElement.clientWidth,
          window.innerWidth || 0
        )
      }
      return (size / 100) * value
    } else {
      // if is an explicit pixel unit, we get rid of the unit and keep the value
      // if is an implicit unit, it's px, and we return just the value
      return value
    }
  }

  /**
   * Parse an `offset` string to extrapolate `x` and `y` numeric offsets.
   * @function
   * @memberof {modifiers~offset}
   * @private
   * @argument {String} offset
   * @argument {Object} popperOffsets
   * @argument {Object} referenceOffsets
   * @argument {String} basePlacement
   * @returns {Array} a two cells array with x and y offsets in numbers
   */
  function parseOffset(offset, popperOffsets, referenceOffsets, basePlacement) {
    var offsets = [0, 0]

    // Use height if placement is left or right and index is 0 otherwise use width
    // in this way the first offset will use an axis and the second one
    // will use the other one
    var useHeight = ['right', 'left'].indexOf(basePlacement) !== -1

    // Split the offset string to obtain a list of values and operands
    // The regex addresses values with the plus or minus sign in front (+10, -20, etc)
    var fragments = offset.split(/(\+|\-)/).map(function(frag) {
      return frag.trim()
    })

    // Detect if the offset string contains a pair of values or a single one
    // they could be separated by comma or space
    var divider = fragments.indexOf(
      find$1(fragments, function(frag) {
        return frag.search(/,|\s/) !== -1
      })
    )

    if (fragments[divider] && fragments[divider].indexOf(',') === -1) {
      console.warn(
        'Offsets separated by white space(s) are deprecated, use a comma (,) instead.'
      )
    }

    // If divider is found, we divide the list of values and operands to divide
    // them by ofset X and Y.
    var splitRegex = /\s*,\s*|\s+/
    var ops =
      divider !== -1
        ? [
            fragments
              .slice(0, divider)
              .concat([fragments[divider].split(splitRegex)[0]]),
            [fragments[divider].split(splitRegex)[1]].concat(
              fragments.slice(divider + 1)
            ),
          ]
        : [fragments]

    // Convert the values with units to absolute pixels to allow our computations
    ops = ops.map(function(op, index) {
      // Most of the units rely on the orientation of the popper
      var measurement = (index === 1
      ? !useHeight
      : useHeight)
        ? 'height'
        : 'width'
      var mergeWithPrevious = false
      return (
        op
          // This aggregates any `+` or `-` sign that aren't considered operators
          // e.g.: 10 + +5 => [10, +, +5]
          .reduce(function(a, b) {
            if (a[a.length - 1] === '' && ['+', '-'].indexOf(b) !== -1) {
              a[a.length - 1] = b
              mergeWithPrevious = true
              return a
            } else if (mergeWithPrevious) {
              a[a.length - 1] += b
              mergeWithPrevious = false
              return a
            } else {
              return a.concat(b)
            }
          }, [])
          // Here we convert the string values into number values (in px)
          .map(function(str) {
            return toValue(str, measurement, popperOffsets, referenceOffsets)
          })
      )
    })

    // Loop trough the offsets arrays and execute the operations
    ops.forEach(function(op, index) {
      op.forEach(function(frag, index2) {
        if (isNumeric(frag)) {
          offsets[index] += frag * (op[index2 - 1] === '-' ? -1 : 1)
        }
      })
    })
    return offsets
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by update method
   * @argument {Object} options - Modifiers configuration and options
   * @argument {Number|String} options.offset=0
   * The offset value as described in the modifier description
   * @returns {Object} The data object, properly modified
   */
  function offset$1(data, _ref) {
    var offset = _ref.offset
    var placement = data.placement,
      _data$offsets = data.offsets,
      popper = _data$offsets.popper,
      reference = _data$offsets.reference

    var basePlacement = placement.split('-')[0]

    var offsets = void 0
    if (isNumeric(+offset)) {
      offsets = [+offset, 0]
    } else {
      offsets = parseOffset(offset, popper, reference, basePlacement)
    }

    if (basePlacement === 'left') {
      popper.top += offsets[0]
      popper.left -= offsets[1]
    } else if (basePlacement === 'right') {
      popper.top += offsets[0]
      popper.left += offsets[1]
    } else if (basePlacement === 'top') {
      popper.left += offsets[0]
      popper.top -= offsets[1]
    } else if (basePlacement === 'bottom') {
      popper.left += offsets[0]
      popper.top += offsets[1]
    }

    data.popper = popper
    return data
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by `update` method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function preventOverflow(data, options) {
    var boundariesElement =
      options.boundariesElement || getOffsetParent(data.instance.popper)

    // If offsetParent is the reference element, we really want to
    // go one step up and use the next offsetParent as reference to
    // avoid to make this modifier completely useless and look like broken
    if (data.instance.reference === boundariesElement) {
      boundariesElement = getOffsetParent(boundariesElement)
    }

    // NOTE: DOM access here
    // resets the popper's position so that the document size can be calculated excluding
    // the size of the popper element itself
    var transformProp = getSupportedPropertyName('transform')
    var popperStyles = data.instance.popper.style // assignment to help minification
    var top = popperStyles.top,
      left = popperStyles.left,
      transform = popperStyles[transformProp]

    popperStyles.top = ''
    popperStyles.left = ''
    popperStyles[transformProp] = ''

    var boundaries = getBoundaries(
      data.instance.popper,
      data.instance.reference,
      options.padding,
      boundariesElement,
      data.positionFixed
    )

    // NOTE: DOM access here
    // restores the original style properties after the offsets have been computed
    popperStyles.top = top
    popperStyles.left = left
    popperStyles[transformProp] = transform

    options.boundaries = boundaries

    var order = options.priority
    var popper = data.offsets.popper

    var check = {
      primary: function primary(placement) {
        var value = popper[placement]
        if (
          popper[placement] < boundaries[placement] &&
          !options.escapeWithReference
        ) {
          value = Math.max(popper[placement], boundaries[placement])
        }
        return defineProperty$1({}, placement, value)
      },
      secondary: function secondary(placement) {
        var mainSide = placement === 'right' ? 'left' : 'top'
        var value = popper[mainSide]
        if (
          popper[placement] > boundaries[placement] &&
          !options.escapeWithReference
        ) {
          value = Math.min(
            popper[mainSide],
            boundaries[placement] -
              (placement === 'right' ? popper.width : popper.height)
          )
        }
        return defineProperty$1({}, mainSide, value)
      },
    }

    order.forEach(function(placement) {
      var side =
        ['left', 'top'].indexOf(placement) !== -1 ? 'primary' : 'secondary'
      popper = _extends$1({}, popper, check[side](placement))
    })

    data.offsets.popper = popper

    return data
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by `update` method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function shift(data) {
    var placement = data.placement
    var basePlacement = placement.split('-')[0]
    var shiftvariation = placement.split('-')[1]

    // if shift shiftvariation is specified, run the modifier
    if (shiftvariation) {
      var _data$offsets = data.offsets,
        reference = _data$offsets.reference,
        popper = _data$offsets.popper

      var isVertical = ['bottom', 'top'].indexOf(basePlacement) !== -1
      var side = isVertical ? 'left' : 'top'
      var measurement = isVertical ? 'width' : 'height'

      var shiftOffsets = {
        start: defineProperty$1({}, side, reference[side]),
        end: defineProperty$1(
          {},
          side,
          reference[side] + reference[measurement] - popper[measurement]
        ),
      }

      data.offsets.popper = _extends$1({}, popper, shiftOffsets[shiftvariation])
    }

    return data
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by update method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function hide(data) {
    if (
      !isModifierRequired(data.instance.modifiers, 'hide', 'preventOverflow')
    ) {
      return data
    }

    var refRect = data.offsets.reference
    var bound = find$1(data.instance.modifiers, function(modifier) {
      return modifier.name === 'preventOverflow'
    }).boundaries

    if (
      refRect.bottom < bound.top ||
      refRect.left > bound.right ||
      refRect.top > bound.bottom ||
      refRect.right < bound.left
    ) {
      // Avoid unnecessary DOM access if visibility hasn't changed
      if (data.hide === true) {
        return data
      }

      data.hide = true
      data.attributes['x-out-of-boundaries'] = ''
    } else {
      // Avoid unnecessary DOM access if visibility hasn't changed
      if (data.hide === false) {
        return data
      }

      data.hide = false
      data.attributes['x-out-of-boundaries'] = false
    }

    return data
  }

  /**
   * @function
   * @memberof Modifiers
   * @argument {Object} data - The data object generated by `update` method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {Object} The data object, properly modified
   */
  function inner(data) {
    var placement = data.placement
    var basePlacement = placement.split('-')[0]
    var _data$offsets = data.offsets,
      popper = _data$offsets.popper,
      reference = _data$offsets.reference

    var isHoriz = ['left', 'right'].indexOf(basePlacement) !== -1

    var subtractLength = ['top', 'left'].indexOf(basePlacement) === -1

    popper[isHoriz ? 'left' : 'top'] =
      reference[basePlacement] -
      (subtractLength ? popper[isHoriz ? 'width' : 'height'] : 0)

    data.placement = getOppositePlacement(placement)
    data.offsets.popper = getClientRect(popper)

    return data
  }

  /**
   * Modifier function, each modifier can have a function of this type assigned
   * to its `fn` property.<br />
   * These functions will be called on each update, this means that you must
   * make sure they are performant enough to avoid performance bottlenecks.
   *
   * @function ModifierFn
   * @argument {dataObject} data - The data object generated by `update` method
   * @argument {Object} options - Modifiers configuration and options
   * @returns {dataObject} The data object, properly modified
   */

  /**
   * Modifiers are plugins used to alter the behavior of your poppers.<br />
   * Popper.js uses a set of 9 modifiers to provide all the basic functionalities
   * needed by the library.
   *
   * Usually you don't want to override the `order`, `fn` and `onLoad` props.
   * All the other properties are configurations that could be tweaked.
   * @namespace modifiers
   */
  var modifiers = {
    /**
     * Modifier used to shift the popper on the start or end of its reference
     * element.<br />
     * It will read the variation of the `placement` property.<br />
     * It can be one either `-end` or `-start`.
     * @memberof modifiers
     * @inner
     */
    shift: {
      /** @prop {number} order=100 - Index used to define the order of execution */
      order: 100,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: shift,
    },

    /**
     * The `offset` modifier can shift your popper on both its axis.
     *
     * It accepts the following units:
     * - `px` or unit-less, interpreted as pixels
     * - `%` or `%r`, percentage relative to the length of the reference element
     * - `%p`, percentage relative to the length of the popper element
     * - `vw`, CSS viewport width unit
     * - `vh`, CSS viewport height unit
     *
     * For length is intended the main axis relative to the placement of the popper.<br />
     * This means that if the placement is `top` or `bottom`, the length will be the
     * `width`. In case of `left` or `right`, it will be the `height`.
     *
     * You can provide a single value (as `Number` or `String`), or a pair of values
     * as `String` divided by a comma or one (or more) white spaces.<br />
     * The latter is a deprecated method because it leads to confusion and will be
     * removed in v2.<br />
     * Additionally, it accepts additions and subtractions between different units.
     * Note that multiplications and divisions aren't supported.
     *
     * Valid examples are:
     * ```
     * 10
     * '10%'
     * '10, 10'
     * '10%, 10'
     * '10 + 10%'
     * '10 - 5vh + 3%'
     * '-10px + 5vh, 5px - 6%'
     * ```
     * > **NB**: If you desire to apply offsets to your poppers in a way that may make them overlap
     * > with their reference element, unfortunately, you will have to disable the `flip` modifier.
     * > You can read more on this at this [issue](https://github.com/FezVrasta/popper.js/issues/373).
     *
     * @memberof modifiers
     * @inner
     */
    offset: {
      /** @prop {number} order=200 - Index used to define the order of execution */
      order: 200,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: offset$1,
      /** @prop {Number|String} offset=0
       * The offset value as described in the modifier description
       */
      offset: 0,
    },

    /**
     * Modifier used to prevent the popper from being positioned outside the boundary.
     *
     * A scenario exists where the reference itself is not within the boundaries.<br />
     * We can say it has "escaped the boundaries" — or just "escaped".<br />
     * In this case we need to decide whether the popper should either:
     *
     * - detach from the reference and remain "trapped" in the boundaries, or
     * - if it should ignore the boundary and "escape with its reference"
     *
     * When `escapeWithReference` is set to`true` and reference is completely
     * outside its boundaries, the popper will overflow (or completely leave)
     * the boundaries in order to remain attached to the edge of the reference.
     *
     * @memberof modifiers
     * @inner
     */
    preventOverflow: {
      /** @prop {number} order=300 - Index used to define the order of execution */
      order: 300,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: preventOverflow,
      /**
       * @prop {Array} [priority=['left','right','top','bottom']]
       * Popper will try to prevent overflow following these priorities by default,
       * then, it could overflow on the left and on top of the `boundariesElement`
       */
      priority: ['left', 'right', 'top', 'bottom'],
      /**
       * @prop {number} padding=5
       * Amount of pixel used to define a minimum distance between the boundaries
       * and the popper. This makes sure the popper always has a little padding
       * between the edges of its container
       */
      padding: 5,
      /**
       * @prop {String|HTMLElement} boundariesElement='scrollParent'
       * Boundaries used by the modifier. Can be `scrollParent`, `window`,
       * `viewport` or any DOM element.
       */
      boundariesElement: 'scrollParent',
    },

    /**
     * Modifier used to make sure the reference and its popper stay near each other
     * without leaving any gap between the two. Especially useful when the arrow is
     * enabled and you want to ensure that it points to its reference element.
     * It cares only about the first axis. You can still have poppers with margin
     * between the popper and its reference element.
     * @memberof modifiers
     * @inner
     */
    keepTogether: {
      /** @prop {number} order=400 - Index used to define the order of execution */
      order: 400,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: keepTogether,
    },

    /**
     * This modifier is used to move the `arrowElement` of the popper to make
     * sure it is positioned between the reference element and its popper element.
     * It will read the outer size of the `arrowElement` node to detect how many
     * pixels of conjunction are needed.
     *
     * It has no effect if no `arrowElement` is provided.
     * @memberof modifiers
     * @inner
     */
    arrow: {
      /** @prop {number} order=500 - Index used to define the order of execution */
      order: 500,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: arrow,
      /** @prop {String|HTMLElement} element='[x-arrow]' - Selector or node used as arrow */
      element: '[x-arrow]',
    },

    /**
     * Modifier used to flip the popper's placement when it starts to overlap its
     * reference element.
     *
     * Requires the `preventOverflow` modifier before it in order to work.
     *
     * **NOTE:** this modifier will interrupt the current update cycle and will
     * restart it if it detects the need to flip the placement.
     * @memberof modifiers
     * @inner
     */
    flip: {
      /** @prop {number} order=600 - Index used to define the order of execution */
      order: 600,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: flip$1,
      /**
       * @prop {String|Array} behavior='flip'
       * The behavior used to change the popper's placement. It can be one of
       * `flip`, `clockwise`, `counterclockwise` or an array with a list of valid
       * placements (with optional variations)
       */
      behavior: 'flip',
      /**
       * @prop {number} padding=5
       * The popper will flip if it hits the edges of the `boundariesElement`
       */
      padding: 5,
      /**
       * @prop {String|HTMLElement} boundariesElement='viewport'
       * The element which will define the boundaries of the popper position.
       * The popper will never be placed outside of the defined boundaries
       * (except if `keepTogether` is enabled)
       */
      boundariesElement: 'viewport',
      /**
       * @prop {Boolean} flipVariations=false
       * The popper will switch placement variation between `-start` and `-end` when
       * the reference element overlaps its boundaries.
       *
       * The original placement should have a set variation.
       */
      flipVariations: false,
      /**
       * @prop {Boolean} flipVariationsByContent=false
       * The popper will switch placement variation between `-start` and `-end` when
       * the popper element overlaps its reference boundaries.
       *
       * The original placement should have a set variation.
       */
      flipVariationsByContent: false,
    },

    /**
     * Modifier used to make the popper flow toward the inner of the reference element.
     * By default, when this modifier is disabled, the popper will be placed outside
     * the reference element.
     * @memberof modifiers
     * @inner
     */
    inner: {
      /** @prop {number} order=700 - Index used to define the order of execution */
      order: 700,
      /** @prop {Boolean} enabled=false - Whether the modifier is enabled or not */
      enabled: false,
      /** @prop {ModifierFn} */
      fn: inner,
    },

    /**
     * Modifier used to hide the popper when its reference element is outside of the
     * popper boundaries. It will set a `x-out-of-boundaries` attribute which can
     * be used to hide with a CSS selector the popper when its reference is
     * out of boundaries.
     *
     * Requires the `preventOverflow` modifier before it in order to work.
     * @memberof modifiers
     * @inner
     */
    hide: {
      /** @prop {number} order=800 - Index used to define the order of execution */
      order: 800,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: hide,
    },

    /**
     * Computes the style that will be applied to the popper element to gets
     * properly positioned.
     *
     * Note that this modifier will not touch the DOM, it just prepares the styles
     * so that `applyStyle` modifier can apply it. This separation is useful
     * in case you need to replace `applyStyle` with a custom implementation.
     *
     * This modifier has `850` as `order` value to maintain backward compatibility
     * with previous versions of Popper.js. Expect the modifiers ordering method
     * to change in future major versions of the library.
     *
     * @memberof modifiers
     * @inner
     */
    computeStyle: {
      /** @prop {number} order=850 - Index used to define the order of execution */
      order: 850,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: computeStyle,
      /**
       * @prop {Boolean} gpuAcceleration=true
       * If true, it uses the CSS 3D transformation to position the popper.
       * Otherwise, it will use the `top` and `left` properties
       */
      gpuAcceleration: true,
      /**
       * @prop {string} [x='bottom']
       * Where to anchor the X axis (`bottom` or `top`). AKA X offset origin.
       * Change this if your popper should grow in a direction different from `bottom`
       */
      x: 'bottom',
      /**
       * @prop {string} [x='left']
       * Where to anchor the Y axis (`left` or `right`). AKA Y offset origin.
       * Change this if your popper should grow in a direction different from `right`
       */
      y: 'right',
    },

    /**
     * Applies the computed styles to the popper element.
     *
     * All the DOM manipulations are limited to this modifier. This is useful in case
     * you want to integrate Popper.js inside a framework or view library and you
     * want to delegate all the DOM manipulations to it.
     *
     * Note that if you disable this modifier, you must make sure the popper element
     * has its position set to `absolute` before Popper.js can do its work!
     *
     * Just disable this modifier and define your own to achieve the desired effect.
     *
     * @memberof modifiers
     * @inner
     */
    applyStyle: {
      /** @prop {number} order=900 - Index used to define the order of execution */
      order: 900,
      /** @prop {Boolean} enabled=true - Whether the modifier is enabled or not */
      enabled: true,
      /** @prop {ModifierFn} */
      fn: applyStyle,
      /** @prop {Function} */
      onLoad: applyStyleOnLoad,
      /**
       * @deprecated since version 1.10.0, the property moved to `computeStyle` modifier
       * @prop {Boolean} gpuAcceleration=true
       * If true, it uses the CSS 3D transformation to position the popper.
       * Otherwise, it will use the `top` and `left` properties
       */
      gpuAcceleration: undefined,
    },
  }

  /**
   * The `dataObject` is an object containing all the information used by Popper.js.
   * This object is passed to modifiers and to the `onCreate` and `onUpdate` callbacks.
   * @name dataObject
   * @property {Object} data.instance The Popper.js instance
   * @property {String} data.placement Placement applied to popper
   * @property {String} data.originalPlacement Placement originally defined on init
   * @property {Boolean} data.flipped True if popper has been flipped by flip modifier
   * @property {Boolean} data.hide True if the reference element is out of boundaries, useful to know when to hide the popper
   * @property {HTMLElement} data.arrowElement Node used as arrow by arrow modifier
   * @property {Object} data.styles Any CSS property defined here will be applied to the popper. It expects the JavaScript nomenclature (eg. `marginBottom`)
   * @property {Object} data.arrowStyles Any CSS property defined here will be applied to the popper arrow. It expects the JavaScript nomenclature (eg. `marginBottom`)
   * @property {Object} data.boundaries Offsets of the popper boundaries
   * @property {Object} data.offsets The measurements of popper, reference and arrow elements
   * @property {Object} data.offsets.popper `top`, `left`, `width`, `height` values
   * @property {Object} data.offsets.reference `top`, `left`, `width`, `height` values
   * @property {Object} data.offsets.arrow] `top` and `left` offsets, only one of them will be different from 0
   */

  /**
   * Default options provided to Popper.js constructor.<br />
   * These can be overridden using the `options` argument of Popper.js.<br />
   * To override an option, simply pass an object with the same
   * structure of the `options` object, as the 3rd argument. For example:
   * ```
   * new Popper(ref, pop, {
   *   modifiers: {
   *     preventOverflow: { enabled: false }
   *   }
   * })
   * ```
   * @type {Object}
   * @static
   * @memberof Popper
   */
  var Defaults = {
    /**
     * Popper's placement.
     * @prop {Popper.placements} placement='bottom'
     */
    placement: 'bottom',

    /**
     * Set this to true if you want popper to position it self in 'fixed' mode
     * @prop {Boolean} positionFixed=false
     */
    positionFixed: false,

    /**
     * Whether events (resize, scroll) are initially enabled.
     * @prop {Boolean} eventsEnabled=true
     */
    eventsEnabled: true,

    /**
     * Set to true if you want to automatically remove the popper when
     * you call the `destroy` method.
     * @prop {Boolean} removeOnDestroy=false
     */
    removeOnDestroy: false,

    /**
     * Callback called when the popper is created.<br />
     * By default, it is set to no-op.<br />
     * Access Popper.js instance with `data.instance`.
     * @prop {onCreate}
     */
    onCreate: function onCreate() {},

    /**
     * Callback called when the popper is updated. This callback is not called
     * on the initialization/creation of the popper, but only on subsequent
     * updates.<br />
     * By default, it is set to no-op.<br />
     * Access Popper.js instance with `data.instance`.
     * @prop {onUpdate}
     */
    onUpdate: function onUpdate() {},

    /**
     * List of modifiers used to modify the offsets before they are applied to the popper.
     * They provide most of the functionalities of Popper.js.
     * @prop {modifiers}
     */
    modifiers: modifiers,
  }

  /**
   * @callback onCreate
   * @param {dataObject} data
   */

  /**
   * @callback onUpdate
   * @param {dataObject} data
   */

  // Utils
  // Methods
  var Popper = (function() {
    /**
     * Creates a new Popper.js instance.
     * @class Popper
     * @param {Element|referenceObject} reference - The reference element used to position the popper
     * @param {Element} popper - The HTML / XML element used as the popper
     * @param {Object} options - Your custom options to override the ones defined in [Defaults](#defaults)
     * @return {Object} instance - The generated Popper.js instance
     */
    function Popper(reference, popper) {
      var _this = this

      var options =
        arguments.length > 2 && arguments[2] !== undefined ? arguments[2] : {}
      classCallCheck(this, Popper)

      this.scheduleUpdate = function() {
        return requestAnimationFrame(_this.update)
      }

      // make update() debounced, so that it only runs at most once-per-tick
      this.update = debounce$1(this.update.bind(this))

      // with {} we create a new object with the options inside it
      this.options = _extends$1({}, Popper.Defaults, options)

      // init state
      this.state = {
        isDestroyed: false,
        isCreated: false,
        scrollParents: [],
      }

      // get reference and popper elements (allow jQuery wrappers)
      this.reference = reference && reference.jquery ? reference[0] : reference
      this.popper = popper && popper.jquery ? popper[0] : popper

      // Deep merge modifiers options
      this.options.modifiers = {}
      Object.keys(
        _extends$1({}, Popper.Defaults.modifiers, options.modifiers)
      ).forEach(function(name) {
        _this.options.modifiers[name] = _extends$1(
          {},
          Popper.Defaults.modifiers[name] || {},
          options.modifiers ? options.modifiers[name] : {}
        )
      })

      // Refactoring modifiers' list (Object => Array)
      this.modifiers = Object.keys(this.options.modifiers)
        .map(function(name) {
          return _extends$1(
            {
              name: name,
            },
            _this.options.modifiers[name]
          )
        })
        // sort the modifiers by order
        .sort(function(a, b) {
          return a.order - b.order
        })

      // modifiers have the ability to execute arbitrary code when Popper.js get inited
      // such code is executed in the same order of its modifier
      // they could add new properties to their options configuration
      // BE AWARE: don't add options to `options.modifiers.name` but to `modifierOptions`!
      this.modifiers.forEach(function(modifierOptions) {
        if (modifierOptions.enabled && isFunction$1(modifierOptions.onLoad)) {
          modifierOptions.onLoad(
            _this.reference,
            _this.popper,
            _this.options,
            modifierOptions,
            _this.state
          )
        }
      })

      // fire the first update to position the popper in the right place
      this.update()

      var eventsEnabled = this.options.eventsEnabled
      if (eventsEnabled) {
        // setup event listeners, they will take care of update the position in specific situations
        this.enableEventListeners()
      }

      this.state.eventsEnabled = eventsEnabled
    }

    // We can't use class properties because they don't get listed in the
    // class prototype and break stuff like Sinon stubs

    createClass(Popper, [
      {
        key: 'update',
        value: function update$$1() {
          return update$1.call(this)
        },
      },
      {
        key: 'destroy',
        value: function destroy$$1() {
          return destroy.call(this)
        },
      },
      {
        key: 'enableEventListeners',
        value: function enableEventListeners$$1() {
          return enableEventListeners.call(this)
        },
      },
      {
        key: 'disableEventListeners',
        value: function disableEventListeners$$1() {
          return disableEventListeners.call(this)
        },

        /**
         * Schedules an update. It will run on the next UI update available.
         * @method scheduleUpdate
         * @memberof Popper
         */

        /**
         * Collection of utilities useful when writing custom modifiers.
         * Starting from version 1.7, this method is available only if you
         * include `popper-utils.js` before `popper.js`.
         *
         * **DEPRECATION**: This way to access PopperUtils is deprecated
         * and will be removed in v2! Use the PopperUtils module directly instead.
         * Due to the high instability of the methods contained in Utils, we can't
         * guarantee them to follow semver. Use them at your own risk!
         * @static
         * @private
         * @type {Object}
         * @deprecated since version 1.8
         * @member Utils
         * @memberof Popper
         */
      },
    ])
    return Popper
  })()

  /**
   * The `referenceObject` is an object that provides an interface compatible with Popper.js
   * and lets you use it as replacement of a real DOM node.<br />
   * You can use this method to position a popper relatively to a set of coordinates
   * in case you don't have a DOM node to use as reference.
   *
   * ```
   * new Popper(referenceObject, popperNode);
   * ```
   *
   * NB: This feature isn't supported in Internet Explorer 10.
   * @name referenceObject
   * @property {Function} data.getBoundingClientRect
   * A function that returns a set of coordinates compatible with the native `getBoundingClientRect` method.
   * @property {number} data.clientWidth
   * An ES6 getter that will return the width of the virtual reference element.
   * @property {number} data.clientHeight
   * An ES6 getter that will return the height of the virtual reference element.
   */

  Popper.Utils = (typeof window !== 'undefined' ? window : global).PopperUtils
  Popper.placements = placements
  Popper.Defaults = Defaults

  /**
   * A convenience hook around `useState` designed to be paired with
   * the component [callback ref](https://reactjs.org/docs/refs-and-the-dom.html#callback-refs) api.
   * Callback refs are useful over `useRef()` when you need to respond to the ref being set
   * instead of lazily accessing it in an effect.
   *
   * ```ts
   * const [element, attachRef] = useCallbackRef<HTMLDivElement>()
   *
   * useEffect(() => {
   *   if (!element) return
   *
   *   const calendar = new FullCalendar.Calendar(element)
   *
   *   return () => {
   *     calendar.destroy()
   *   }
   * }, [element])
   *
   * return <div ref={attachRef} />
   * ```
   */

  function useCallbackRef() {
    return React.useState(null)
  }

  var toFnRef = function toFnRef(ref) {
    return !ref || typeof ref === 'function'
      ? ref
      : function(value) {
          ref.current = value
        }
  }

  function mergeRefs(refA, refB) {
    var a = toFnRef(refA)
    var b = toFnRef(refB)
    return function(value) {
      if (a) a(value)
      if (b) b(value)
    }
  }
  /**
   * Create and returns a single callback ref composed from two other Refs.
   *
   * ```tsx
   * const Button = React.forwardRef((props, ref) => {
   *   const [element, attachRef] = useCallbackRef<HTMLButtonElement>();
   *   const mergedRef = useMergedRefs(ref, attachRef);
   *
   *   return <button ref={mergedRef} {...props}/>
   * })
   * ```
   *
   * @param refA A Callback or mutable Ref
   * @param refB A Callback or mutable Ref
   */

  function useMergedRefs(refA, refB) {
    return React.useMemo(
      function() {
        return mergeRefs(refA, refB)
      },
      [refA, refB]
    )
  }

  var initialPopperStyles = {
    position: 'absolute',
    top: '0',
    left: '0',
    opacity: '0',
    pointerEvents: 'none',
  }
  var initialArrowStyles = {}
  /**
   * Position an element relative some reference element using Popper.js
   *
   * @param {HTMLElement} referenceElement The element
   * @param {HTMLElement} popperElement
   * @param {Object}      options
   * @param {Object}      options.modifiers Popper.js modifiers
   * @param {Boolean}     options.enabled toggle the popper functionality on/off
   * @param {String}      options.placement The popper element placement relative to the reference element
   * @param {Boolean}     options.positionFixed use fixed positioning
   * @param {Boolean}     options.eventsEnabled have Popper listen on window resize events to reposition the element
   */

  function usePopper(referenceElement, popperElement, _temp) {
    var _ref = _temp === void 0 ? {} : _temp,
      _ref$enabled = _ref.enabled,
      enabled = _ref$enabled === void 0 ? true : _ref$enabled,
      _ref$placement = _ref.placement,
      placement = _ref$placement === void 0 ? 'bottom' : _ref$placement,
      _ref$positionFixed = _ref.positionFixed,
      positionFixed =
        _ref$positionFixed === void 0 ? false : _ref$positionFixed,
      _ref$eventsEnabled = _ref.eventsEnabled,
      eventsEnabled = _ref$eventsEnabled === void 0 ? true : _ref$eventsEnabled,
      _ref$modifiers = _ref.modifiers,
      modifiers = _ref$modifiers === void 0 ? {} : _ref$modifiers

    var popperInstanceRef = React.useRef()
    var hasArrow = !!(modifiers.arrow && modifiers.arrow.element)
    var scheduleUpdate = React.useCallback(function() {
      if (popperInstanceRef.current) {
        popperInstanceRef.current.scheduleUpdate()
      }
    }, [])

    var _useState = React.useState({
        placement: placement,
        scheduleUpdate: scheduleUpdate,
        outOfBoundaries: false,
        styles: initialPopperStyles,
        arrowStyles: initialArrowStyles,
      }),
      state = _useState[0],
      setState = _useState[1] // A placement difference in state means popper determined a new placement
    // apart from the props value. By the time the popper element is rendered with
    // the new position Popper has already measured it, if the place change triggers
    // a size change it will result in a misaligned popper. So we schedule an update to be sure.

    React.useEffect(
      function() {
        scheduleUpdate()
      },
      [state.placement, scheduleUpdate]
    )
    /** Toggle Events */

    React.useEffect(
      function() {
        if (popperInstanceRef.current) {
          // eslint-disable-next-line no-unused-expressions
          eventsEnabled
            ? popperInstanceRef.current.enableEventListeners()
            : popperInstanceRef.current.disableEventListeners()
        }
      },
      [eventsEnabled]
    )
    React.useEffect(
      function() {
        if (!enabled || referenceElement === null || popperElement === null) {
          return undefined
        }

        var arrow =
          modifiers.arrow &&
          _extends({}, modifiers.arrow, {
            element: modifiers.arrow.element,
          })

        popperInstanceRef.current = new Popper(
          referenceElement,
          popperElement,
          {
            placement: placement,
            positionFixed: positionFixed,
            modifiers: _extends({}, modifiers, {
              arrow: arrow,
              applyStyle: {
                enabled: false,
              },
              updateStateModifier: {
                enabled: true,
                order: 900,
                fn: function fn(data) {
                  setState({
                    scheduleUpdate: scheduleUpdate,
                    styles: _extends(
                      {
                        position: data.offsets.popper.position,
                      },
                      data.styles
                    ),
                    arrowStyles: data.arrowStyles,
                    outOfBoundaries: data.hide,
                    placement: data.placement,
                  })
                },
              },
            }),
          }
        )
        return function() {
          if (popperInstanceRef.current !== null) {
            popperInstanceRef.current.destroy()
            popperInstanceRef.current = null
          }
        } // intentionally NOT re-running on new modifiers
        // eslint-disable-next-line react-hooks/exhaustive-deps
      },
      [
        enabled,
        placement,
        positionFixed,
        referenceElement,
        popperElement,
        hasArrow,
      ]
    )
    return state
  }

  /* eslint-disable no-return-assign */
  var optionsSupported = false
  var onceSupported = false

  try {
    var options = {
      get passive() {
        return (optionsSupported = true)
      },

      get once() {
        // eslint-disable-next-line no-multi-assign
        return (onceSupported = optionsSupported = true)
      },
    }

    if (canUseDOM) {
      window.addEventListener('test', options, options)
      window.removeEventListener('test', options, true)
    }
  } catch (e) {
    /* */
  }

  /**
   * An `addEventListener` ponyfill, supports the `once` option
   */
  function addEventListener(node, eventName, handler, options) {
    if (options && typeof options !== 'boolean' && !onceSupported) {
      var once = options.once,
        capture = options.capture
      var wrappedHandler = handler

      if (!onceSupported && once) {
        wrappedHandler =
          handler.__once ||
          function onceHandler(event) {
            this.removeEventListener(eventName, onceHandler, capture)
            handler.call(this, event)
          }

        handler.__once = wrappedHandler
      }

      node.addEventListener(
        eventName,
        wrappedHandler,
        optionsSupported ? options : capture
      )
    }

    node.addEventListener(eventName, handler, options)
  }

  function removeEventListener(node, eventName, handler, options) {
    var capture =
      options && typeof options !== 'boolean' ? options.capture : options
    node.removeEventListener(eventName, handler, capture)

    if (handler.__once) {
      node.removeEventListener(eventName, handler.__once, capture)
    }
  }

  function listen(node, eventName, handler, options) {
    addEventListener(node, eventName, handler, options)
    return function() {
      removeEventListener(node, eventName, handler, options)
    }
  }

  /**
   * Creates a `Ref` whose value is updated in an effect, ensuring the most recent
   * value is the one rendered with. Generally only required for Concurrent mode usage
   * where previous work in `render()` may be discarded befor being used.
   *
   * This is safe to access in an event handler.
   *
   * @param value The `Ref` value
   */

  function useCommittedRef(value) {
    var ref = React.useRef(value)
    React.useEffect(
      function() {
        ref.current = value
      },
      [value]
    )
    return ref
  }

  function useEventCallback(fn) {
    var ref = useCommittedRef(fn)
    return React.useCallback(
      function() {
        return ref.current && ref.current.apply(ref, arguments)
      },
      [ref]
    )
  }

  var escapeKeyCode = 27

  var noop$2 = function noop() {}

  function isLeftClickEvent(event) {
    return event.button === 0
  }

  function isModifiedEvent(event) {
    return !!(event.metaKey || event.altKey || event.ctrlKey || event.shiftKey)
  }
  /**
   * The `useRootClose` hook registers your callback on the document
   * when rendered. Powers the `<Overlay/>` component. This is used achieve modal
   * style behavior where your callback is triggered when the user tries to
   * interact with the rest of the document or hits the `esc` key.
   *
   * @param {Ref<HTMLElement>|HTMLElement} ref  The element boundary
   * @param {function} onRootClose
   * @param {object}  options
   * @param {boolean} options.disabled
   * @param {string}  options.clickTrigger The DOM event name (click, mousedown, etc) to attach listeners on
   */

  function useRootClose(ref, onRootClose, _temp) {
    var _ref = _temp === void 0 ? {} : _temp,
      disabled = _ref.disabled,
      _ref$clickTrigger = _ref.clickTrigger,
      clickTrigger = _ref$clickTrigger === void 0 ? 'click' : _ref$clickTrigger

    var preventMouseRootCloseRef = React.useRef(false)
    var onClose = onRootClose || noop$2
    var handleMouseCapture = React.useCallback(
      function(e) {
        var currentTarget = ref && ('current' in ref ? ref.current : ref)
        warning_1(
          !!currentTarget,
          'RootClose captured a close event but does not have a ref to compare it to. ' +
            'useRootClose(), should be passed a ref that resolves to a DOM node'
        )
        preventMouseRootCloseRef.current =
          !currentTarget ||
          isModifiedEvent(e) ||
          !isLeftClickEvent(e) ||
          contains(currentTarget, e.target)
      },
      [ref]
    )
    var handleMouse = useEventCallback(function(e) {
      if (!preventMouseRootCloseRef.current) {
        onClose(e)
      }
    })
    var handleKeyUp = useEventCallback(function(e) {
      if (e.keyCode === escapeKeyCode) {
        onClose(e)
      }
    })
    React.useEffect(
      function() {
        if (disabled || ref == null) return undefined // Use capture for this listener so it fires before React's listener, to
        // avoid false positives in the contains() check below if the target DOM
        // element is removed in the React mouse callback.

        var removeMouseCaptureListener = listen(
          document,
          clickTrigger,
          handleMouseCapture,
          true
        )
        var removeMouseListener = listen(document, clickTrigger, handleMouse)
        var removeKeyupListener = listen(document, 'keyup', handleKeyUp)
        var mobileSafariHackListeners = []

        if ('ontouchstart' in document.documentElement) {
          mobileSafariHackListeners = [].slice
            .call(document.body.children)
            .map(function(el) {
              return listen(el, 'mousemove', noop$2)
            })
        }

        return function() {
          removeMouseCaptureListener()
          removeMouseListener()
          removeKeyupListener()
          mobileSafariHackListeners.forEach(function(remove) {
            return remove()
          })
        }
      },
      [
        ref,
        disabled,
        clickTrigger,
        handleMouseCapture,
        handleMouse,
        handleKeyUp,
      ]
    )
  }

  var resolveRef = function resolveRef(ref) {
    if (typeof document === 'undefined') return undefined
    if (ref == null) return ownerDocument().body
    if (typeof ref === 'function') ref = ref()
    if (ref && ref.current) ref = ref.current
    if (ref && ref.nodeType) return ref
    return null
  }

  function useWaitForDOMRef(ref, onResolved) {
    var _useState = React.useState(function() {
        return resolveRef(ref)
      }),
      resolvedRef = _useState[0],
      setRef = _useState[1]

    if (!resolvedRef) {
      var earlyRef = resolveRef(ref)
      if (earlyRef) setRef(earlyRef)
    }

    React.useEffect(
      function() {
        if (onResolved && resolvedRef) {
          onResolved(resolvedRef)
        }
      },
      [onResolved, resolvedRef]
    )
    React.useEffect(
      function() {
        var nextRef = resolveRef(ref)

        if (nextRef !== resolvedRef) {
          setRef(nextRef)
        }
      },
      [ref, resolvedRef]
    )
    return resolvedRef
  }

  /**
   * Built on top of `Popper.js`, the overlay component is
   * great for custom tooltip overlays.
   */

  var Overlay = React__default.forwardRef(function(props, outerRef) {
    var flip = props.flip,
      placement = props.placement,
      containerPadding = props.containerPadding,
      _props$popperConfig = props.popperConfig,
      popperConfig = _props$popperConfig === void 0 ? {} : _props$popperConfig,
      Transition = props.transition

    var _useCallbackRef = useCallbackRef(),
      rootElement = _useCallbackRef[0],
      attachRef = _useCallbackRef[1]

    var _useCallbackRef2 = useCallbackRef(),
      arrowElement = _useCallbackRef2[0],
      attachArrowRef = _useCallbackRef2[1]

    var mergedRef = useMergedRefs(attachRef, outerRef)
    var container = useWaitForDOMRef(props.container)
    var target = useWaitForDOMRef(props.target)

    var _useState = React.useState(!props.show),
      exited = _useState[0],
      setExited = _useState[1]

    var _popperConfig$modifie = popperConfig.modifiers,
      modifiers = _popperConfig$modifie === void 0 ? {} : _popperConfig$modifie

    var _usePopper = usePopper(
        target,
        rootElement,
        _extends({}, popperConfig, {
          placement: placement || 'bottom',
          enableEvents: props.show,
          modifiers: _extends({}, modifiers, {
            preventOverflow: _extends(
              {
                padding: containerPadding || 5,
              },
              modifiers.preventOverflow
            ),
            arrow: _extends({}, modifiers.arrow, {
              enabled: !!arrowElement,
              element: arrowElement,
            }),
            flip: _extends(
              {
                enabled: !!flip,
              },
              modifiers.preventOverflow
            ),
          }),
        })
      ),
      styles = _usePopper.styles,
      arrowStyles = _usePopper.arrowStyles,
      popper = _objectWithoutPropertiesLoose(_usePopper, [
        'styles',
        'arrowStyles',
      ])

    if (props.show) {
      if (exited) setExited(false)
    } else if (!props.transition && !exited) {
      setExited(true)
    }

    var handleHidden = function handleHidden() {
      setExited(true)

      if (props.onExited) {
        props.onExited.apply(props, arguments)
      }
    } // Don't un-render the overlay while it's transitioning out.

    var mountOverlay = props.show || (Transition && !exited)
    useRootClose(rootElement, props.onHide, {
      disabled: !props.rootClose || props.rootCloseDisabled,
      clickTrigger: props.rootCloseEvent,
    })

    if (!mountOverlay) {
      // Don't bother showing anything if we don't have to.
      return null
    }

    var child = props.children(
      _extends({}, popper, {
        show: props.show,
        props: {
          style: styles,
          ref: mergedRef,
        },
        arrowProps: {
          style: arrowStyles,
          ref: attachArrowRef,
        },
      })
    )

    if (Transition) {
      var onExit = props.onExit,
        onExiting = props.onExiting,
        onEnter = props.onEnter,
        onEntering = props.onEntering,
        onEntered = props.onEntered
      child = React__default.createElement(
        Transition,
        {
          in: props.show,
          appear: true,
          onExit: onExit,
          onExiting: onExiting,
          onExited: handleHidden,
          onEnter: onEnter,
          onEntering: onEntering,
          onEntered: onEntered,
        },
        child
      )
    }

    return container ? ReactDOM__default.createPortal(child, container) : null
  })
  Overlay.displayName = 'Overlay'
  Overlay.propTypes = {
    /**
     * Set the visibility of the Overlay
     */
    show: propTypes.bool,

    /** Specify where the overlay element is positioned in relation to the target element */
    placement: propTypes.oneOf(Popper.placements),

    /**
     * A DOM Element, Ref to an element, or function that returns either. The `target` element is where
     * the overlay is positioned relative to.
     */
    target: propTypes.any,

    /**
     * A DOM Element, Ref to an element, or function that returns either. The `container` will have the Portal children
     * appended to it.
     */
    container: propTypes.any,

    /**
     * Enables the Popper.js `flip` modifier, allowing the Overlay to
     * automatically adjust it's placement in case of overlap with the viewport or toggle.
     * Refer to the [flip docs](https://popper.js.org/popper-documentation.html#modifiers..flip.enabled) for more info
     */
    flip: propTypes.bool,

    /**
     * A render prop that returns an element to overlay and position. See
     * the [react-popper documentation](https://github.com/FezVrasta/react-popper#children) for more info.
     *
     * @type {Function ({
     *   show: boolean,
     *   placement: Placement,
     *   outOfBoundaries: ?boolean,
     *   scheduleUpdate: () => void,
     *   props: {
     *     ref: (?HTMLElement) => void,
     *     style: { [string]: string | number },
     *     aria-labelledby: ?string
     *   },
     *   arrowProps: {
     *     ref: (?HTMLElement) => void,
     *     style: { [string]: string | number },
     *   },
     * }) => React.Element}
     */
    children: propTypes.func.isRequired,

    /**
     * Control how much space there is between the edge of the boundary element and overlay.
     * A convenience shortcut to setting `popperConfig.modfiers.preventOverflow.padding`
     */
    containerPadding: propTypes.number,

    /**
     * A set of popper options and props passed directly to react-popper's Popper component.
     */
    popperConfig: propTypes.object,

    /**
     * Specify whether the overlay should trigger `onHide` when the user clicks outside the overlay
     */
    rootClose: propTypes.bool,

    /**
     * Specify event for toggling overlay
     */
    rootCloseEvent: propTypes.oneOf(['click', 'mousedown']),

    /**
     * Specify disabled for disable RootCloseWrapper
     */
    rootCloseDisabled: propTypes.bool,

    /**
     * A Callback fired by the Overlay when it wishes to be hidden.
     *
     * __required__ when `rootClose` is `true`.
     *
     * @type func
     */
    onHide: function onHide(props) {
      var propType = propTypes.func

      if (props.rootClose) {
        propType = propType.isRequired
      }

      for (
        var _len = arguments.length,
          args = new Array(_len > 1 ? _len - 1 : 0),
          _key = 1;
        _key < _len;
        _key++
      ) {
        args[_key - 1] = arguments[_key]
      }

      return propType.apply(void 0, [props].concat(args))
    },

    /**
     * A `react-transition-group@2.0.0` `<Transition/>` component
     * used to animate the overlay as it changes visibility.
     */
    transition: propTypes.elementType,

    /**
     * Callback fired before the Overlay transitions in
     */
    onEnter: propTypes.func,

    /**
     * Callback fired as the Overlay begins to transition in
     */
    onEntering: propTypes.func,

    /**
     * Callback fired after the Overlay finishes transitioning in
     */
    onEntered: propTypes.func,

    /**
     * Callback fired right before the Overlay transitions out
     */
    onExit: propTypes.func,

    /**
     * Callback fired as the Overlay begins to transition out
     */
    onExiting: propTypes.func,

    /**
     * Callback fired after the Overlay finishes transitioning out
     */
    onExited: propTypes.func,
  }
  Overlay.defaultProps = {
    containerPadding: 5,
  }

  function height(node, client) {
    var win = isWindow(node)
    return win
      ? win.innerHeight
      : client
      ? node.clientHeight
      : offset(node).height
  }

  var toArray$1 = Function.prototype.bind.call(
    Function.prototype.call,
    [].slice
  )
  function qsa(element, selector) {
    return toArray$1(element.querySelectorAll(selector))
  }

  var matchesImpl
  function matches$1(node, selector) {
    if (!matchesImpl) {
      var body = document.body
      var nativeMatch =
        body.matches ||
        body.matchesSelector ||
        body.webkitMatchesSelector ||
        body.mozMatchesSelector ||
        body.msMatchesSelector

      matchesImpl = function matchesImpl(n, s) {
        return nativeMatch.call(n, s)
      }
    }

    return matchesImpl(node, selector)
  }

  function closest(node, selector, stopAt) {
    if (node.closest && !stopAt) node.closest(selector)
    var nextNode = node

    do {
      if (matches$1(nextNode, selector)) return nextNode
      nextNode = nextNode.parentElement
    } while (nextNode && nextNode !== stopAt && nextNode.nodeType === document.ELEMENT_NODE)

    return null
  }

  function addEventListener$1(type, handler, target) {
    if (target === void 0) {
      target = document
    }

    return listen(target, type, handler, {
      passive: false,
    })
  }

  function isOverContainer(container, x, y) {
    return !container || contains(container, document.elementFromPoint(x, y))
  }

  function getEventNodeFromPoint(node, _ref) {
    var clientX = _ref.clientX,
      clientY = _ref.clientY
    var target = document.elementFromPoint(clientX, clientY)
    return closest(target, '.rbc-event', node)
  }
  function isEvent(node, bounds) {
    return !!getEventNodeFromPoint(node, bounds)
  }

  function getEventCoordinates(e) {
    var target = e

    if (e.touches && e.touches.length) {
      target = e.touches[0]
    }

    return {
      clientX: target.clientX,
      clientY: target.clientY,
      pageX: target.pageX,
      pageY: target.pageY,
    }
  }

  var clickTolerance = 5
  var clickInterval = 250

  var Selection =
    /*#__PURE__*/
    (function() {
      function Selection(node, _temp) {
        var _ref2 = _temp === void 0 ? {} : _temp,
          _ref2$global = _ref2.global,
          global = _ref2$global === void 0 ? false : _ref2$global,
          _ref2$longPressThresh = _ref2.longPressThreshold,
          longPressThreshold =
            _ref2$longPressThresh === void 0 ? 250 : _ref2$longPressThresh

        this.isDetached = false
        this.container = node
        this.globalMouse = !node || global
        this.longPressThreshold = longPressThreshold
        this._listeners = Object.create(null)
        this._handleInitialEvent = this._handleInitialEvent.bind(this)
        this._handleMoveEvent = this._handleMoveEvent.bind(this)
        this._handleTerminatingEvent = this._handleTerminatingEvent.bind(this)
        this._keyListener = this._keyListener.bind(this)
        this._dropFromOutsideListener = this._dropFromOutsideListener.bind(this)
        this._dragOverFromOutsideListener = this._dragOverFromOutsideListener.bind(
          this
        ) // Fixes an iOS 10 bug where scrolling could not be prevented on the window.
        // https://github.com/metafizzy/flickity/issues/457#issuecomment-254501356

        this._removeTouchMoveWindowListener = addEventListener$1(
          'touchmove',
          function() {},
          window
        )
        this._removeKeyDownListener = addEventListener$1(
          'keydown',
          this._keyListener
        )
        this._removeKeyUpListener = addEventListener$1(
          'keyup',
          this._keyListener
        )
        this._removeDropFromOutsideListener = addEventListener$1(
          'drop',
          this._dropFromOutsideListener
        )
        this._onDragOverfromOutisde = addEventListener$1(
          'dragover',
          this._dragOverFromOutsideListener
        )

        this._addInitialEventListener()
      }

      var _proto = Selection.prototype

      _proto.on = function on(type, handler) {
        var handlers = this._listeners[type] || (this._listeners[type] = [])
        handlers.push(handler)
        return {
          remove: function remove() {
            var idx = handlers.indexOf(handler)
            if (idx !== -1) handlers.splice(idx, 1)
          },
        }
      }

      _proto.emit = function emit(type) {
        for (
          var _len = arguments.length,
            args = new Array(_len > 1 ? _len - 1 : 0),
            _key = 1;
          _key < _len;
          _key++
        ) {
          args[_key - 1] = arguments[_key]
        }

        var result
        var handlers = this._listeners[type] || []
        handlers.forEach(function(fn) {
          if (result === undefined) result = fn.apply(void 0, args)
        })
        return result
      }

      _proto.teardown = function teardown() {
        this.isDetached = true
        this.listeners = Object.create(null)
        this._removeTouchMoveWindowListener &&
          this._removeTouchMoveWindowListener()
        this._removeInitialEventListener && this._removeInitialEventListener()
        this._removeEndListener && this._removeEndListener()
        this._onEscListener && this._onEscListener()
        this._removeMoveListener && this._removeMoveListener()
        this._removeKeyUpListener && this._removeKeyUpListener()
        this._removeKeyDownListener && this._removeKeyDownListener()
        this._removeDropFromOutsideListener &&
          this._removeDropFromOutsideListener()
      }

      _proto.isSelected = function isSelected(node) {
        var box = this._selectRect
        if (!box || !this.selecting) return false
        return objectsCollide(box, getBoundsForNode(node))
      }

      _proto.filter = function filter(items) {
        var box = this._selectRect //not selecting

        if (!box || !this.selecting) return []
        return items.filter(this.isSelected, this)
      } // Adds a listener that will call the handler only after the user has pressed on the screen
      // without moving their finger for 250ms.

      _proto._addLongPressListener = function _addLongPressListener(
        handler,
        initialEvent
      ) {
        var _this = this

        var timer = null
        var removeTouchMoveListener = null
        var removeTouchEndListener = null

        var handleTouchStart = function handleTouchStart(initialEvent) {
          timer = setTimeout(function() {
            cleanup()
            handler(initialEvent)
          }, _this.longPressThreshold)
          removeTouchMoveListener = addEventListener$1('touchmove', function() {
            return cleanup()
          })
          removeTouchEndListener = addEventListener$1('touchend', function() {
            return cleanup()
          })
        }

        var removeTouchStartListener = addEventListener$1(
          'touchstart',
          handleTouchStart
        )

        var cleanup = function cleanup() {
          if (timer) {
            clearTimeout(timer)
          }

          if (removeTouchMoveListener) {
            removeTouchMoveListener()
          }

          if (removeTouchEndListener) {
            removeTouchEndListener()
          }

          timer = null
          removeTouchMoveListener = null
          removeTouchEndListener = null
        }

        if (initialEvent) {
          handleTouchStart(initialEvent)
        }

        return function() {
          cleanup()
          removeTouchStartListener()
        }
      } // Listen for mousedown and touchstart events. When one is received, disable the other and setup
      // future event handling based on the type of event.

      _proto._addInitialEventListener = function _addInitialEventListener() {
        var _this2 = this

        var removeMouseDownListener = addEventListener$1('mousedown', function(
          e
        ) {
          _this2._removeInitialEventListener()

          _this2._handleInitialEvent(e)

          _this2._removeInitialEventListener = addEventListener$1(
            'mousedown',
            _this2._handleInitialEvent
          )
        })
        var removeTouchStartListener = addEventListener$1(
          'touchstart',
          function(e) {
            _this2._removeInitialEventListener()

            _this2._removeInitialEventListener = _this2._addLongPressListener(
              _this2._handleInitialEvent,
              e
            )
          }
        )

        this._removeInitialEventListener = function() {
          removeMouseDownListener()
          removeTouchStartListener()
        }
      }

      _proto._dropFromOutsideListener = function _dropFromOutsideListener(e) {
        var _getEventCoordinates = getEventCoordinates(e),
          pageX = _getEventCoordinates.pageX,
          pageY = _getEventCoordinates.pageY,
          clientX = _getEventCoordinates.clientX,
          clientY = _getEventCoordinates.clientY

        this.emit('dropFromOutside', {
          x: pageX,
          y: pageY,
          clientX: clientX,
          clientY: clientY,
        })
        e.preventDefault()
      }

      _proto._dragOverFromOutsideListener = function _dragOverFromOutsideListener(
        e
      ) {
        var _getEventCoordinates2 = getEventCoordinates(e),
          pageX = _getEventCoordinates2.pageX,
          pageY = _getEventCoordinates2.pageY,
          clientX = _getEventCoordinates2.clientX,
          clientY = _getEventCoordinates2.clientY

        this.emit('dragOverFromOutside', {
          x: pageX,
          y: pageY,
          clientX: clientX,
          clientY: clientY,
        })
        e.preventDefault()
      }

      _proto._handleInitialEvent = function _handleInitialEvent(e) {
        if (this.isDetached) {
          return
        }

        var _getEventCoordinates3 = getEventCoordinates(e),
          clientX = _getEventCoordinates3.clientX,
          clientY = _getEventCoordinates3.clientY,
          pageX = _getEventCoordinates3.pageX,
          pageY = _getEventCoordinates3.pageY

        var node = this.container(),
          collides,
          offsetData // Right clicks

        if (
          e.which === 3 ||
          e.button === 2 ||
          !isOverContainer(node, clientX, clientY)
        )
          return

        if (!this.globalMouse && node && !contains(node, e.target)) {
          var _normalizeDistance = normalizeDistance(0),
            top = _normalizeDistance.top,
            left = _normalizeDistance.left,
            bottom = _normalizeDistance.bottom,
            right = _normalizeDistance.right

          offsetData = getBoundsForNode(node)
          collides = objectsCollide(
            {
              top: offsetData.top - top,
              left: offsetData.left - left,
              bottom: offsetData.bottom + bottom,
              right: offsetData.right + right,
            },
            {
              top: pageY,
              left: pageX,
            }
          )
          if (!collides) return
        }

        var result = this.emit(
          'beforeSelect',
          (this._initialEventData = {
            isTouch: /^touch/.test(e.type),
            x: pageX,
            y: pageY,
            clientX: clientX,
            clientY: clientY,
          })
        )
        if (result === false) return

        switch (e.type) {
          case 'mousedown':
            this._removeEndListener = addEventListener$1(
              'mouseup',
              this._handleTerminatingEvent
            )
            this._onEscListener = addEventListener$1(
              'keydown',
              this._handleTerminatingEvent
            )
            this._removeMoveListener = addEventListener$1(
              'mousemove',
              this._handleMoveEvent
            )
            break

          case 'touchstart':
            this._handleMoveEvent(e)

            this._removeEndListener = addEventListener$1(
              'touchend',
              this._handleTerminatingEvent
            )
            this._removeMoveListener = addEventListener$1(
              'touchmove',
              this._handleMoveEvent
            )
            break

          default:
            break
        }
      }

      _proto._handleTerminatingEvent = function _handleTerminatingEvent(e) {
        var _getEventCoordinates4 = getEventCoordinates(e),
          pageX = _getEventCoordinates4.pageX,
          pageY = _getEventCoordinates4.pageY

        this.selecting = false
        this._removeEndListener && this._removeEndListener()
        this._removeMoveListener && this._removeMoveListener()
        if (!this._initialEventData) return
        var inRoot = !this.container || contains(this.container(), e.target)
        var bounds = this._selectRect
        var click = this.isClick(pageX, pageY)
        this._initialEventData = null

        if (e.key === 'Escape') {
          return this.emit('reset')
        }

        if (!inRoot) {
          return this.emit('reset')
        }

        if (click && inRoot) {
          return this._handleClickEvent(e)
        } // User drag-clicked in the Selectable area

        if (!click) return this.emit('select', bounds)
      }

      _proto._handleClickEvent = function _handleClickEvent(e) {
        var _getEventCoordinates5 = getEventCoordinates(e),
          pageX = _getEventCoordinates5.pageX,
          pageY = _getEventCoordinates5.pageY,
          clientX = _getEventCoordinates5.clientX,
          clientY = _getEventCoordinates5.clientY

        var now = new Date().getTime()

        if (
          this._lastClickData &&
          now - this._lastClickData.timestamp < clickInterval
        ) {
          // Double click event
          this._lastClickData = null
          return this.emit('doubleClick', {
            x: pageX,
            y: pageY,
            clientX: clientX,
            clientY: clientY,
          })
        } // Click event

        this._lastClickData = {
          timestamp: now,
        }
        return this.emit('click', {
          x: pageX,
          y: pageY,
          clientX: clientX,
          clientY: clientY,
        })
      }

      _proto._handleMoveEvent = function _handleMoveEvent(e) {
        if (this._initialEventData === null || this.isDetached) {
          return
        }

        var _this$_initialEventDa = this._initialEventData,
          x = _this$_initialEventDa.x,
          y = _this$_initialEventDa.y

        var _getEventCoordinates6 = getEventCoordinates(e),
          pageX = _getEventCoordinates6.pageX,
          pageY = _getEventCoordinates6.pageY

        var w = Math.abs(x - pageX)
        var h = Math.abs(y - pageY)
        var left = Math.min(pageX, x),
          top = Math.min(pageY, y),
          old = this.selecting // Prevent emitting selectStart event until mouse is moved.
        // in Chrome on Windows, mouseMove event may be fired just after mouseDown event.

        if (this.isClick(pageX, pageY) && !old && !(w || h)) {
          return
        }

        this.selecting = true
        this._selectRect = {
          top: top,
          left: left,
          x: pageX,
          y: pageY,
          right: left + w,
          bottom: top + h,
        }

        if (!old) {
          this.emit('selectStart', this._initialEventData)
        }

        if (!this.isClick(pageX, pageY))
          this.emit('selecting', this._selectRect)
        e.preventDefault()
      }

      _proto._keyListener = function _keyListener(e) {
        this.ctrl = e.metaKey || e.ctrlKey
      }

      _proto.isClick = function isClick(pageX, pageY) {
        var _this$_initialEventDa2 = this._initialEventData,
          x = _this$_initialEventDa2.x,
          y = _this$_initialEventDa2.y,
          isTouch = _this$_initialEventDa2.isTouch
        return (
          !isTouch &&
          Math.abs(pageX - x) <= clickTolerance &&
          Math.abs(pageY - y) <= clickTolerance
        )
      }

      return Selection
    })()
  /**
   * Resolve the disance prop from either an Int or an Object
   * @return {Object}
   */

  function normalizeDistance(distance) {
    if (distance === void 0) {
      distance = 0
    }

    if (typeof distance !== 'object')
      distance = {
        top: distance,
        left: distance,
        right: distance,
        bottom: distance,
      }
    return distance
  }
  /**
   * Given two objects containing "top", "left", "offsetWidth" and "offsetHeight"
   * properties, determine if they collide.
   * @param  {Object|HTMLElement} a
   * @param  {Object|HTMLElement} b
   * @return {bool}
   */

  function objectsCollide(nodeA, nodeB, tolerance) {
    if (tolerance === void 0) {
      tolerance = 0
    }

    var _getBoundsForNode = getBoundsForNode(nodeA),
      aTop = _getBoundsForNode.top,
      aLeft = _getBoundsForNode.left,
      _getBoundsForNode$rig = _getBoundsForNode.right,
      aRight = _getBoundsForNode$rig === void 0 ? aLeft : _getBoundsForNode$rig,
      _getBoundsForNode$bot = _getBoundsForNode.bottom,
      aBottom = _getBoundsForNode$bot === void 0 ? aTop : _getBoundsForNode$bot

    var _getBoundsForNode2 = getBoundsForNode(nodeB),
      bTop = _getBoundsForNode2.top,
      bLeft = _getBoundsForNode2.left,
      _getBoundsForNode2$ri = _getBoundsForNode2.right,
      bRight = _getBoundsForNode2$ri === void 0 ? bLeft : _getBoundsForNode2$ri,
      _getBoundsForNode2$bo = _getBoundsForNode2.bottom,
      bBottom = _getBoundsForNode2$bo === void 0 ? bTop : _getBoundsForNode2$bo

    return !// 'a' bottom doesn't touch 'b' top
    (
      aBottom - tolerance < bTop || // 'a' top doesn't touch 'b' bottom
      aTop + tolerance > bBottom || // 'a' right doesn't touch 'b' left
      aRight - tolerance < bLeft || // 'a' left doesn't touch 'b' right
      aLeft + tolerance > bRight
    )
  }
  /**
   * Given a node, get everything needed to calculate its boundaries
   * @param  {HTMLElement} node
   * @return {Object}
   */

  function getBoundsForNode(node) {
    if (!node.getBoundingClientRect) return node
    var rect = node.getBoundingClientRect(),
      left = rect.left + pageOffset('left'),
      top = rect.top + pageOffset('top')
    return {
      top: top,
      left: left,
      right: (node.offsetWidth || 0) + left,
      bottom: (node.offsetHeight || 0) + top,
    }
  }

  function pageOffset(dir) {
    if (dir === 'left')
      return window.pageXOffset || document.body.scrollLeft || 0
    if (dir === 'top') return window.pageYOffset || document.body.scrollTop || 0
  }

  var BackgroundCells =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(BackgroundCells, _React$Component)

      function BackgroundCells(props, context) {
        var _this

        _this = _React$Component.call(this, props, context) || this
        _this.state = {
          selecting: false,
        }
        return _this
      }

      var _proto = BackgroundCells.prototype

      _proto.componentDidMount = function componentDidMount() {
        this.props.selectable && this._selectable()
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        this._teardownSelectable()
      }

      _proto.componentWillReceiveProps = function componentWillReceiveProps(
        nextProps
      ) {
        if (nextProps.selectable && !this.props.selectable) this._selectable()
        if (!nextProps.selectable && this.props.selectable)
          this._teardownSelectable()
      }

      _proto.render = function render() {
        var _this$props = this.props,
          range = _this$props.range,
          getNow = _this$props.getNow,
          getters = _this$props.getters,
          currentDate = _this$props.date,
          Wrapper = _this$props.components.dateCellWrapper
        var _this$state = this.state,
          selecting = _this$state.selecting,
          startIdx = _this$state.startIdx,
          endIdx = _this$state.endIdx
        var current = getNow()
        return React__default.createElement(
          'div',
          {
            className: 'rbc-row-bg',
          },
          range.map(function(date, index) {
            var selected = selecting && index >= startIdx && index <= endIdx

            var _getters$dayProp = getters.dayProp(date),
              className = _getters$dayProp.className,
              style = _getters$dayProp.style

            return React__default.createElement(
              Wrapper,
              {
                key: index,
                value: date,
                range: range,
              },
              React__default.createElement('div', {
                style: style,
                className: clsx(
                  'rbc-day-bg',
                  className,
                  selected && 'rbc-selected-cell',
                  eq(date, current, 'day') && 'rbc-today',
                  currentDate &&
                    month(currentDate) !== month(date) &&
                    'rbc-off-range-bg'
                ),
              })
            )
          })
        )
      }

      _proto._selectable = function _selectable() {
        var _this2 = this

        var node = ReactDOM.findDOMNode(this)
        var selector = (this._selector = new Selection(this.props.container, {
          longPressThreshold: this.props.longPressThreshold,
        }))

        var selectorClicksHandler = function selectorClicksHandler(
          point,
          actionType
        ) {
          if (!isEvent(ReactDOM.findDOMNode(_this2), point)) {
            var rowBox = getBoundsForNode(node)
            var _this2$props = _this2.props,
              range = _this2$props.range,
              rtl = _this2$props.rtl

            if (pointInBox(rowBox, point)) {
              var currentCell = getSlotAtX(rowBox, point.x, rtl, range.length)

              _this2._selectSlot({
                startIdx: currentCell,
                endIdx: currentCell,
                action: actionType,
                box: point,
              })
            }
          }

          _this2._initial = {}

          _this2.setState({
            selecting: false,
          })
        }

        selector.on('selecting', function(box) {
          var _this2$props2 = _this2.props,
            range = _this2$props2.range,
            rtl = _this2$props2.rtl
          var startIdx = -1
          var endIdx = -1

          if (!_this2.state.selecting) {
            notify(_this2.props.onSelectStart, [box])
            _this2._initial = {
              x: box.x,
              y: box.y,
            }
          }

          if (selector.isSelected(node)) {
            var nodeBox = getBoundsForNode(node)

            var _dateCellSelection = dateCellSelection(
              _this2._initial,
              nodeBox,
              box,
              range.length,
              rtl
            )

            startIdx = _dateCellSelection.startIdx
            endIdx = _dateCellSelection.endIdx
          }

          _this2.setState({
            selecting: true,
            startIdx: startIdx,
            endIdx: endIdx,
          })
        })
        selector.on('beforeSelect', function(box) {
          if (_this2.props.selectable !== 'ignoreEvents') return
          return !isEvent(ReactDOM.findDOMNode(_this2), box)
        })
        selector.on('click', function(point) {
          return selectorClicksHandler(point, 'click')
        })
        selector.on('doubleClick', function(point) {
          return selectorClicksHandler(point, 'doubleClick')
        })
        selector.on('select', function(bounds) {
          _this2._selectSlot(
            _extends({}, _this2.state, {
              action: 'select',
              bounds: bounds,
            })
          )

          _this2._initial = {}

          _this2.setState({
            selecting: false,
          })

          notify(_this2.props.onSelectEnd, [_this2.state])
        })
      }

      _proto._teardownSelectable = function _teardownSelectable() {
        if (!this._selector) return

        this._selector.teardown()

        this._selector = null
      }

      _proto._selectSlot = function _selectSlot(_ref) {
        var endIdx = _ref.endIdx,
          startIdx = _ref.startIdx,
          action = _ref.action,
          bounds = _ref.bounds,
          box = _ref.box
        if (endIdx !== -1 && startIdx !== -1)
          this.props.onSelectSlot &&
            this.props.onSelectSlot({
              start: startIdx,
              end: endIdx,
              action: action,
              bounds: bounds,
              box: box,
            })
      }

      return BackgroundCells
    })(React__default.Component)

  BackgroundCells.propTypes = {
    date: propTypes.instanceOf(Date),
    getNow: propTypes.func.isRequired,
    getters: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    container: propTypes.func,
    dayPropGetter: propTypes.func,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onSelectSlot: propTypes.func.isRequired,
    onSelectEnd: propTypes.func,
    onSelectStart: propTypes.func,
    range: propTypes.arrayOf(propTypes.instanceOf(Date)),
    rtl: propTypes.bool,
    type: propTypes.string,
  }

  /* eslint-disable react/prop-types */

  var EventRowMixin = {
    propTypes: {
      slotMetrics: propTypes.object.isRequired,
      selected: propTypes.object,
      isAllDay: propTypes.bool,
      accessors: propTypes.object.isRequired,
      localizer: propTypes.object.isRequired,
      components: propTypes.object.isRequired,
      getters: propTypes.object.isRequired,
      onSelect: propTypes.func,
      onDoubleClick: propTypes.func,
    },
    defaultProps: {
      segments: [],
      selected: {},
    },
    renderEvent: function renderEvent(props, event) {
      var selected = props.selected,
        _ = props.isAllDay,
        accessors = props.accessors,
        getters = props.getters,
        onSelect = props.onSelect,
        onDoubleClick = props.onDoubleClick,
        localizer = props.localizer,
        slotMetrics = props.slotMetrics,
        components = props.components
      var continuesPrior = slotMetrics.continuesPrior(event)
      var continuesAfter = slotMetrics.continuesAfter(event)
      return React__default.createElement(EventCell, {
        event: event,
        getters: getters,
        localizer: localizer,
        accessors: accessors,
        components: components,
        onSelect: onSelect,
        onDoubleClick: onDoubleClick,
        continuesPrior: continuesPrior,
        continuesAfter: continuesAfter,
        slotStart: slotMetrics.first,
        slotEnd: slotMetrics.last,
        selected: isSelected(event, selected),
      })
    },
    renderSpan: function renderSpan(slots, len, key, content) {
      if (content === void 0) {
        content = ' '
      }

      var per = (Math.abs(len) / slots) * 100 + '%'
      return React__default.createElement(
        'div',
        {
          key: key,
          className: 'rbc-row-segment', // IE10/11 need max-width. flex-basis doesn't respect box-sizing
          style: {
            WebkitFlexBasis: per,
            flexBasis: per,
            maxWidth: per,
          },
        },
        content
      )
    },
  }

  var EventRow =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(EventRow, _React$Component)

      function EventRow() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = EventRow.prototype

      _proto.render = function render() {
        var _this = this

        var _this$props = this.props,
          segments = _this$props.segments,
          slots = _this$props.slotMetrics.slots,
          className = _this$props.className
        var lastEnd = 1
        return React__default.createElement(
          'div',
          {
            className: clsx(className, 'rbc-row'),
          },
          segments.reduce(function(row, _ref, li) {
            var event = _ref.event,
              left = _ref.left,
              right = _ref.right,
              span = _ref.span
            var key = '_lvl_' + li
            var gap = left - lastEnd
            var content = EventRowMixin.renderEvent(_this.props, event)
            if (gap)
              row.push(EventRowMixin.renderSpan(slots, gap, key + '_gap'))
            row.push(EventRowMixin.renderSpan(slots, span, key, content))
            lastEnd = right + 1
            return row
          }, [])
        )
      }

      return EventRow
    })(React__default.Component)

  EventRow.propTypes = _extends(
    {
      segments: propTypes.array,
    },
    EventRowMixin.propTypes
  )
  EventRow.defaultProps = _extends({}, EventRowMixin.defaultProps)

  function endOfRange(dateRange, unit) {
    if (unit === void 0) {
      unit = 'day'
    }

    return {
      first: dateRange[0],
      last: add(dateRange[dateRange.length - 1], 1, unit),
    }
  }
  function eventSegments(event, range, accessors) {
    var _endOfRange = endOfRange(range),
      first = _endOfRange.first,
      last = _endOfRange.last

    var slots = diff(first, last, 'day')
    var start = max(startOf(accessors.start(event), 'day'), first)
    var end = min(ceil(accessors.end(event), 'day'), last)
    var padding = findIndex(range, function(x) {
      return eq(x, start, 'day')
    })
    var span = diff(start, end, 'day')
    span = Math.min(span, slots)
    span = Math.max(span, 1)
    return {
      event: event,
      span: span,
      left: padding + 1,
      right: Math.max(padding + span, 1),
    }
  }
  function eventLevels(rowSegments, limit) {
    if (limit === void 0) {
      limit = Infinity
    }

    var i,
      j,
      seg,
      levels = [],
      extra = []

    for (i = 0; i < rowSegments.length; i++) {
      seg = rowSegments[i]

      for (j = 0; j < levels.length; j++) {
        if (!segsOverlap(seg, levels[j])) break
      }

      if (j >= limit) {
        extra.push(seg)
      } else {
        ;(levels[j] || (levels[j] = [])).push(seg)
      }
    }

    for (i = 0; i < levels.length; i++) {
      levels[i].sort(function(a, b) {
        return a.left - b.left
      }) //eslint-disable-line
    }

    return {
      levels: levels,
      extra: extra,
    }
  }
  function inRange$2(e, start, end, accessors) {
    var eStart = startOf(accessors.start(e), 'day')
    var eEnd = accessors.end(e)
    var startsBeforeEnd = lte(eStart, end, 'day') // when the event is zero duration we need to handle a bit differently

    var endsAfterStart = !eq(eStart, eEnd, 'minutes')
      ? gt(eEnd, start, 'minutes')
      : gte(eEnd, start, 'minutes')
    return startsBeforeEnd && endsAfterStart
  }
  function segsOverlap(seg, otherSegs) {
    return otherSegs.some(function(otherSeg) {
      return otherSeg.left <= seg.right && otherSeg.right >= seg.left
    })
  }
  function sortEvents(evtA, evtB, accessors) {
    var startSort =
      +startOf(accessors.start(evtA), 'day') -
      +startOf(accessors.start(evtB), 'day')
    var durA = diff(
      accessors.start(evtA),
      ceil(accessors.end(evtA), 'day'),
      'day'
    )
    var durB = diff(
      accessors.start(evtB),
      ceil(accessors.end(evtB), 'day'),
      'day'
    )
    return (
      startSort || // sort by start Day first
      Math.max(durB, 1) - Math.max(durA, 1) || // events spanning multiple days go first
      !!accessors.allDay(evtB) - !!accessors.allDay(evtA) || // then allDay single day events
      +accessors.start(evtA) - +accessors.start(evtB)
    ) // then sort by start time
  }

  var isSegmentInSlot = function isSegmentInSlot(seg, slot) {
    return seg.left <= slot && seg.right >= slot
  }

  var eventsInSlot = function eventsInSlot(segments, slot) {
    return segments.filter(function(seg) {
      return isSegmentInSlot(seg, slot)
    }).length
  }

  var EventEndingRow =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(EventEndingRow, _React$Component)

      function EventEndingRow() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = EventEndingRow.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          segments = _this$props.segments,
          slots = _this$props.slotMetrics.slots
        var rowSegments = eventLevels(segments).levels[0]
        var current = 1,
          lastEnd = 1,
          row = []

        while (current <= slots) {
          var key = '_lvl_' + current

          var _ref =
              rowSegments.filter(function(seg) {
                return isSegmentInSlot(seg, current)
              })[0] || {},
            event = _ref.event,
            left = _ref.left,
            right = _ref.right,
            span = _ref.span //eslint-disable-line

          if (!event) {
            current++
            continue
          }

          var gap = Math.max(0, left - lastEnd)

          if (this.canRenderSlotEvent(left, span)) {
            var content = EventRowMixin.renderEvent(this.props, event)

            if (gap) {
              row.push(EventRowMixin.renderSpan(slots, gap, key + '_gap'))
            }

            row.push(EventRowMixin.renderSpan(slots, span, key, content))
            lastEnd = current = right + 1
          } else {
            if (gap) {
              row.push(EventRowMixin.renderSpan(slots, gap, key + '_gap'))
            }

            row.push(
              EventRowMixin.renderSpan(
                slots,
                1,
                key,
                this.renderShowMore(segments, current)
              )
            )
            lastEnd = current = current + 1
          }
        }

        return React__default.createElement(
          'div',
          {
            className: 'rbc-row',
          },
          row
        )
      }

      _proto.canRenderSlotEvent = function canRenderSlotEvent(slot, span) {
        var segments = this.props.segments
        return range$1(slot, slot + span).every(function(s) {
          var count = eventsInSlot(segments, s)
          return count === 1
        })
      }

      _proto.renderShowMore = function renderShowMore(segments, slot) {
        var _this = this

        var localizer = this.props.localizer
        var count = eventsInSlot(segments, slot)
        return count
          ? React__default.createElement(
              'a',
              {
                key: 'sm_' + slot,
                href: '#',
                className: 'rbc-show-more',
                onClick: function onClick(e) {
                  return _this.showMore(slot, e)
                },
              },
              localizer.messages.showMore(count)
            )
          : false
      }

      _proto.showMore = function showMore(slot, e) {
        e.preventDefault()
        this.props.onShowMore(slot, e.target)
      }

      return EventEndingRow
    })(React__default.Component)

  EventEndingRow.propTypes = _extends(
    {
      segments: propTypes.array,
      slots: propTypes.number,
      onShowMore: propTypes.func,
    },
    EventRowMixin.propTypes
  )
  EventEndingRow.defaultProps = _extends({}, EventRowMixin.defaultProps)

  var simpleIsEqual = function simpleIsEqual(a, b) {
    return a === b
  }

  function index(resultFn, isEqual) {
    if (isEqual === void 0) {
      isEqual = simpleIsEqual
    }

    var lastThis
    var lastArgs = []
    var lastResult
    var calledOnce = false

    var isNewArgEqualToLast = function isNewArgEqualToLast(newArg, index) {
      return isEqual(newArg, lastArgs[index])
    }

    var result = function result() {
      for (
        var _len = arguments.length, newArgs = new Array(_len), _key = 0;
        _key < _len;
        _key++
      ) {
        newArgs[_key] = arguments[_key]
      }

      if (
        calledOnce &&
        lastThis === this &&
        newArgs.length === lastArgs.length &&
        newArgs.every(isNewArgEqualToLast)
      ) {
        return lastResult
      }

      lastResult = resultFn.apply(this, newArgs)
      calledOnce = true
      lastThis = this
      lastArgs = newArgs
      return lastResult
    }

    return result
  }

  var isSegmentInSlot$1 = function isSegmentInSlot(seg, slot) {
    return seg.left <= slot && seg.right >= slot
  }

  var isEqual$1 = function isEqual(a, b) {
    return a.range === b.range && a.events === b.events
  }

  function getSlotMetrics() {
    return index(function(options) {
      var range = options.range,
        events = options.events,
        maxRows = options.maxRows,
        minRows = options.minRows,
        accessors = options.accessors

      var _endOfRange = endOfRange(range),
        first = _endOfRange.first,
        last = _endOfRange.last

      var segments = events.map(function(evt) {
        return eventSegments(evt, range, accessors)
      })

      var _eventLevels = eventLevels(segments, Math.max(maxRows - 1, 1)),
        levels = _eventLevels.levels,
        extra = _eventLevels.extra

      while (levels.length < minRows) {
        levels.push([])
      }

      return {
        first: first,
        last: last,
        levels: levels,
        extra: extra,
        range: range,
        slots: range.length,
        clone: function clone(args) {
          var metrics = getSlotMetrics()
          return metrics(_extends({}, options, {}, args))
        },
        getDateForSlot: function getDateForSlot(slotNumber) {
          return range[slotNumber]
        },
        getSlotForDate: function getSlotForDate(date) {
          return range.find(function(r) {
            return eq(r, date, 'day')
          })
        },
        getEventsForSlot: function getEventsForSlot(slot) {
          return segments
            .filter(function(seg) {
              return isSegmentInSlot$1(seg, slot)
            })
            .map(function(seg) {
              return seg.event
            })
        },
        continuesPrior: function continuesPrior(event) {
          return lt(accessors.start(event), first, 'day')
        },
        continuesAfter: function continuesAfter(event) {
          var eventEnd = accessors.end(event)
          var singleDayDuration = eq(
            accessors.start(event),
            eventEnd,
            'minutes'
          )
          return singleDayDuration
            ? gte(eventEnd, last, 'minutes')
            : gt(eventEnd, last, 'minutes')
        },
      }
    }, isEqual$1)
  }

  var DateContentRow =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(DateContentRow, _React$Component)

      function DateContentRow() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(args)) ||
          this

        _this.handleSelectSlot = function(slot) {
          var _this$props = _this.props,
            range = _this$props.range,
            onSelectSlot = _this$props.onSelectSlot
          onSelectSlot(range.slice(slot.start, slot.end + 1), slot)
        }

        _this.handleShowMore = function(slot, target) {
          var _this$props2 = _this.props,
            range = _this$props2.range,
            onShowMore = _this$props2.onShowMore

          var metrics = _this.slotMetrics(_this.props)

          var row = qsa(
            ReactDOM.findDOMNode(_assertThisInitialized(_this)),
            '.rbc-row-bg'
          )[0]
          var cell
          if (row) cell = row.children[slot - 1]
          var events = metrics.getEventsForSlot(slot)
          onShowMore(events, range[slot - 1], cell, slot, target)
        }

        _this.createHeadingRef = function(r) {
          _this.headingRow = r
        }

        _this.createEventRef = function(r) {
          _this.eventRow = r
        }

        _this.getContainer = function() {
          var container = _this.props.container
          return container
            ? container()
            : ReactDOM.findDOMNode(_assertThisInitialized(_this))
        }

        _this.renderHeadingCell = function(date, index) {
          var _this$props3 = _this.props,
            renderHeader = _this$props3.renderHeader,
            getNow = _this$props3.getNow
          return renderHeader({
            date: date,
            key: 'header_' + index,
            className: clsx(
              'rbc-date-cell',
              eq(date, getNow(), 'day') && 'rbc-now'
            ),
          })
        }

        _this.renderDummy = function() {
          var _this$props4 = _this.props,
            className = _this$props4.className,
            range = _this$props4.range,
            renderHeader = _this$props4.renderHeader
          return React__default.createElement(
            'div',
            {
              className: className,
            },
            React__default.createElement(
              'div',
              {
                className: 'rbc-row-content',
              },
              renderHeader &&
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-row',
                    ref: _this.createHeadingRef,
                  },
                  range.map(_this.renderHeadingCell)
                ),
              React__default.createElement(
                'div',
                {
                  className: 'rbc-row',
                  ref: _this.createEventRef,
                },
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-row-segment',
                  },
                  React__default.createElement(
                    'div',
                    {
                      className: 'rbc-event',
                    },
                    React__default.createElement(
                      'div',
                      {
                        className: 'rbc-event-content',
                      },
                      '\xA0'
                    )
                  )
                )
              )
            )
          )
        }

        _this.slotMetrics = getSlotMetrics()
        return _this
      }

      var _proto = DateContentRow.prototype

      _proto.getRowLimit = function getRowLimit() {
        var eventHeight = height(this.eventRow)
        var headingHeight = this.headingRow ? height(this.headingRow) : 0
        var eventSpace = height(ReactDOM.findDOMNode(this)) - headingHeight
        return Math.max(Math.floor(eventSpace / eventHeight), 1)
      }

      _proto.render = function render() {
        var _this$props5 = this.props,
          date = _this$props5.date,
          rtl = _this$props5.rtl,
          range = _this$props5.range,
          className = _this$props5.className,
          selected = _this$props5.selected,
          selectable = _this$props5.selectable,
          renderForMeasure = _this$props5.renderForMeasure,
          accessors = _this$props5.accessors,
          getters = _this$props5.getters,
          components = _this$props5.components,
          getNow = _this$props5.getNow,
          renderHeader = _this$props5.renderHeader,
          onSelect = _this$props5.onSelect,
          localizer = _this$props5.localizer,
          onSelectStart = _this$props5.onSelectStart,
          onSelectEnd = _this$props5.onSelectEnd,
          onDoubleClick = _this$props5.onDoubleClick,
          resourceId = _this$props5.resourceId,
          longPressThreshold = _this$props5.longPressThreshold,
          isAllDay = _this$props5.isAllDay
        if (renderForMeasure) return this.renderDummy()
        var metrics = this.slotMetrics(this.props)
        var levels = metrics.levels,
          extra = metrics.extra
        var WeekWrapper = components.weekWrapper
        var eventRowProps = {
          selected: selected,
          accessors: accessors,
          getters: getters,
          localizer: localizer,
          components: components,
          onSelect: onSelect,
          onDoubleClick: onDoubleClick,
          resourceId: resourceId,
          slotMetrics: metrics,
        }
        return React__default.createElement(
          'div',
          {
            className: className,
          },
          React__default.createElement(BackgroundCells, {
            date: date,
            getNow: getNow,
            rtl: rtl,
            range: range,
            selectable: selectable,
            container: this.getContainer,
            getters: getters,
            onSelectStart: onSelectStart,
            onSelectEnd: onSelectEnd,
            onSelectSlot: this.handleSelectSlot,
            components: components,
            longPressThreshold: longPressThreshold,
          }),
          React__default.createElement(
            'div',
            {
              className: 'rbc-row-content',
            },
            renderHeader &&
              React__default.createElement(
                'div',
                {
                  className: 'rbc-row ',
                  ref: this.createHeadingRef,
                },
                range.map(this.renderHeadingCell)
              ),
            React__default.createElement(
              WeekWrapper,
              _extends(
                {
                  isAllDay: isAllDay,
                },
                eventRowProps
              ),
              levels.map(function(segs, idx) {
                return React__default.createElement(
                  EventRow,
                  _extends(
                    {
                      key: idx,
                      segments: segs,
                    },
                    eventRowProps
                  )
                )
              }),
              !!extra.length &&
                React__default.createElement(
                  EventEndingRow,
                  _extends(
                    {
                      segments: extra,
                      onShowMore: this.handleShowMore,
                    },
                    eventRowProps
                  )
                )
            )
          )
        )
      }

      return DateContentRow
    })(React__default.Component)

  DateContentRow.propTypes = {
    date: propTypes.instanceOf(Date),
    events: propTypes.array.isRequired,
    range: propTypes.array.isRequired,
    rtl: propTypes.bool,
    resourceId: propTypes.any,
    renderForMeasure: propTypes.bool,
    renderHeader: propTypes.func,
    container: propTypes.func,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onShowMore: propTypes.func,
    onSelectSlot: propTypes.func,
    onSelect: propTypes.func,
    onSelectEnd: propTypes.func,
    onSelectStart: propTypes.func,
    onDoubleClick: propTypes.func,
    dayPropGetter: propTypes.func,
    getNow: propTypes.func.isRequired,
    isAllDay: propTypes.bool,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    minRows: propTypes.number.isRequired,
    maxRows: propTypes.number.isRequired,
  }
  DateContentRow.defaultProps = {
    minRows: 0,
    maxRows: Infinity,
  }

  var Header = function Header(_ref) {
    var label = _ref.label
    return React__default.createElement('span', null, label)
  }

  Header.propTypes = {
    label: propTypes.node,
  }

  var DateHeader = function DateHeader(_ref) {
    var label = _ref.label,
      drilldownView = _ref.drilldownView,
      onDrillDown = _ref.onDrillDown

    if (!drilldownView) {
      return React__default.createElement('span', null, label)
    }

    return React__default.createElement(
      'a',
      {
        href: '#',
        onClick: onDrillDown,
      },
      label
    )
  }

  DateHeader.propTypes = {
    label: propTypes.node,
    date: propTypes.instanceOf(Date),
    drilldownView: propTypes.string,
    onDrillDown: propTypes.func,
    isOffRange: propTypes.bool,
  }

  // const GestureWrapper = props => {
  //   const _swipeBind = useGesture({
  //     onDrag: throttleHandler,
  //     onScroll: throttleHandler,
  //     onWheel: throttleHandler,
  //     window: window,
  //   })
  //   return (
  //     <div {...props} {..._swipeBind()}>
  //       {props.children}
  //     </div>
  //   )
  // }
  // const handler = ({ wheeling, vxvy: [vx, vy] }) => {
  //   if (!wheeling) {
  //     if (vx <= 0 && vy == 0) {
  //       document.querySelector('#navigate-left').click()
  //     }
  //     if (vx > 0 && vy == 0) {
  //       document.querySelector('#navigate-right').click()
  //     }
  //   }
  // }

  var eventsForWeek = function eventsForWeek(evts, start, end, accessors) {
    return evts.filter(function(e) {
      return inRange$2(e, start, end, accessors)
    })
  }

  var MonthView =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(MonthView, _React$Component)

      function MonthView() {
        var _this

        for (
          var _len = arguments.length, _args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          _args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(_args)) ||
          this

        _this.navigateLeft = function() {
          document.querySelector('#navigate-left').click()
        }

        _this.navigateRight = function() {
          document.querySelector('#navigate-right').click()
        }

        _this.handleCalendarNavigationClick = debounce(
          function(deltaY) {
            if (deltaY > 0) {
              // prev month
              _this.navigateLeft()
            }

            if (deltaY < 0) {
              // next month
              _this.navigateRight()
            }
          },
          100,
          {
            leading: false,
            trailing: true,
          }
        )

        _this.eventWheel = function(e) {
          e.preventDefault()

          _this.handleCalendarNavigationClick(e.deltaY)
        }

        _this.handleCalendarNavigationMobile = debounce(
          function(deltaY) {
            if (deltaY < -90) {
              // next month
              _this.navigateRight()
            }

            if (deltaY > 150) {
              // prev month
              _this.navigateLeft()
            }
          },
          100,
          {
            leading: false,
            trailing: true,
          }
        )

        _this.touchStartHandler = function(e) {
          // e.preventDefault()
          _this.startTouch = e.touches[0].clientY
        }

        _this.touchMoveHandler = function(e) {
          e.preventDefault()
          _this.endTouch = e.touches[0].clientY

          _this.handleCalendarNavigationMobile(
            _this.startTouch - _this.endTouch
          )
        }

        _this.getContainer = function() {
          return ReactDOM.findDOMNode(_assertThisInitialized(_this))
        }

        _this.renderWeek = function(week, weekIdx) {
          var _this$props = _this.props,
            events = _this$props.events,
            components = _this$props.components,
            selectable = _this$props.selectable,
            getNow = _this$props.getNow,
            selected = _this$props.selected,
            date = _this$props.date,
            localizer = _this$props.localizer,
            longPressThreshold = _this$props.longPressThreshold,
            accessors = _this$props.accessors,
            getters = _this$props.getters
          var _this$state = _this.state,
            needLimitMeasure = _this$state.needLimitMeasure,
            rowLimit = _this$state.rowLimit
          events = eventsForWeek(
            events,
            week[0],
            week[week.length - 1],
            accessors
          )
          events.sort(function(a, b) {
            return sortEvents(a, b, accessors)
          })
          return React__default.createElement(DateContentRow, {
            key: weekIdx,
            ref: weekIdx === 0 ? _this.slotRowRef : undefined,
            container: _this.getContainer,
            className: 'rbc-month-row',
            getNow: getNow,
            date: date,
            range: week,
            events: events,
            maxRows: rowLimit,
            selected: selected,
            selectable: selectable,
            components: components,
            accessors: accessors,
            getters: getters,
            localizer: localizer,
            renderHeader: _this.readerDateHeading,
            renderForMeasure: needLimitMeasure,
            onShowMore: _this.handleShowMore,
            onSelect: _this.handleSelectEvent,
            onDoubleClick: _this.handleDoubleClickEvent,
            onSelectSlot: _this.handleSelectSlot,
            longPressThreshold: longPressThreshold,
            rtl: _this.props.rtl,
          })
        }

        _this.readerDateHeading = function(_ref) {
          var date = _ref.date,
            className = _ref.className,
            props = _objectWithoutPropertiesLoose(_ref, ['date', 'className'])

          var _this$props2 = _this.props,
            currentDate = _this$props2.date,
            getDrilldownView = _this$props2.getDrilldownView,
            localizer = _this$props2.localizer
          var isOffRange = month(date) !== month(currentDate)
          var isCurrent = eq(date, currentDate, 'day')
          var drilldownView = getDrilldownView(date)
          var label = localizer.format(date, 'dateFormat')
          var DateHeaderComponent =
            _this.props.components.dateHeader || DateHeader
          return React__default.createElement(
            'div',
            _extends({}, props, {
              className: clsx(
                className,
                isOffRange && 'rbc-off-range',
                isCurrent && 'rbc-current'
              ),
            }),
            React__default.createElement(DateHeaderComponent, {
              label: label,
              date: date,
              drilldownView: drilldownView,
              isOffRange: isOffRange,
              onDrillDown: function onDrillDown(e) {
                return _this.handleHeadingClick(date, drilldownView, e)
              },
            })
          )
        }

        _this.handleSelectSlot = function(range, slotInfo) {
          _this._pendingSelection = _this._pendingSelection.concat(range)
          clearTimeout(_this._selectTimer)
          _this._selectTimer = setTimeout(function() {
            return _this.selectDates(slotInfo)
          })
        }

        _this.handleHeadingClick = function(date, view, e) {
          e.preventDefault()

          _this.clearSelection()

          notify(_this.props.onDrillDown, [date, view])
        }

        _this.handleSelectEvent = function() {
          _this.clearSelection()

          for (
            var _len2 = arguments.length, args = new Array(_len2), _key2 = 0;
            _key2 < _len2;
            _key2++
          ) {
            args[_key2] = arguments[_key2]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this.handleDoubleClickEvent = function() {
          _this.clearSelection()

          for (
            var _len3 = arguments.length, args = new Array(_len3), _key3 = 0;
            _key3 < _len3;
            _key3++
          ) {
            args[_key3] = arguments[_key3]
          }

          notify(_this.props.onDoubleClickEvent, args)
        }

        _this.handleShowMore = function(events, date, cell, slot, target) {
          var _this$props3 = _this.props,
            popup = _this$props3.popup,
            onDrillDown = _this$props3.onDrillDown,
            onShowMore = _this$props3.onShowMore,
            getDrilldownView = _this$props3.getDrilldownView //cancel any pending selections so only the event click goes through.

          _this.clearSelection()

          if (popup) {
            var position$1 = position(
              cell,
              ReactDOM.findDOMNode(_assertThisInitialized(_this))
            )

            _this.setState({
              overlay: {
                date: date,
                events: events,
                position: position$1,
                target: target,
              },
            })
          } else {
            notify(onDrillDown, [date, getDrilldownView(date) || views.DAY])
          }

          notify(onShowMore, [events, date, slot])
        }

        _this._bgRows = []
        _this._pendingSelection = []
        _this.slotRowRef = React__default.createRef()
        _this.state = {
          rowLimit: 5,
          needLimitMeasure: true,
        }
        _this.startTouch = 0
        _this.endTouch = 0
        return _this
      }

      var _proto = MonthView.prototype

      _proto.componentWillReceiveProps = function componentWillReceiveProps(
        _ref2
      ) {
        var date = _ref2.date
        this.setState({
          needLimitMeasure: !eq(date, this.props.date, 'month'),
        })
      }

      _proto.componentDidMount = function componentDidMount() {
        var _this2 = this

        var el = document.getElementById('onWheel')

        if (el) {
          el.addEventListener(
            'wheel',
            (this.onWheel = function(e) {
              return _this2.eventWheel(e)
            }),
            false
          )
          el.addEventListener('touchstart', this.touchStartHandler, false)
          el.addEventListener('touchmove', this.touchMoveHandler, false)
        }

        var running
        if (this.state.needLimitMeasure) this.measureRowLimit(this.props)
        window.addEventListener(
          'resize',
          (this._resizeListener = function() {
            if (!running) {
              request(function() {
                running = false

                _this2.setState({
                  needLimitMeasure: true,
                }) //eslint-disable-line
              })
            }
          }),
          false
        )
      }

      _proto.componentDidUpdate = function componentDidUpdate() {
        if (this.state.needLimitMeasure) this.measureRowLimit(this.props)
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        document.removeEventListener('wheel', this.eventWheel, false)
        document.removeEventListener(
          'touchstart',
          this.touchStartHandler,
          false
        )
        document.removeEventListener('touchmove', this.touchMoveHandler, false)
        window.removeEventListener('resize', this._resizeListener, false)
      }

      _proto.render = function render() {
        var _this$props4 = this.props,
          date = _this$props4.date,
          localizer = _this$props4.localizer,
          className = _this$props4.className,
          month = visibleDays(date, localizer),
          weeks = chunk(month, 7)
        this._weekCount = weeks.length
        return React__default.createElement(
          'div',
          {
            id: 'onWheel',
            className: clsx('rbc-month-view', className),
          },
          React__default.createElement(
            'div',
            {
              className: 'rbc-row rbc-month-header',
            },
            this.renderHeaders(weeks[0])
          ),
          weeks.map(this.renderWeek),
          this.props.popup && this.renderOverlay()
        )
      }

      _proto.renderHeaders = function renderHeaders(row) {
        var _this$props5 = this.props,
          localizer = _this$props5.localizer,
          components = _this$props5.components
        var first = row[0]
        var last = row[row.length - 1]
        var HeaderComponent = components.header || Header
        return range(first, last, 'day').map(function(day, idx) {
          return React__default.createElement(
            'div',
            {
              key: 'header_' + idx,
              className: 'rbc-header',
            },
            React__default.createElement(HeaderComponent, {
              date: day,
              localizer: localizer,
              label: localizer.format(day, 'weekdayFormat'),
            })
          )
        })
      }

      _proto.renderOverlay = function renderOverlay() {
        var _this3 = this

        var overlay = (this.state && this.state.overlay) || {}
        var _this$props6 = this.props,
          accessors = _this$props6.accessors,
          localizer = _this$props6.localizer,
          components = _this$props6.components,
          getters = _this$props6.getters,
          selected = _this$props6.selected,
          popupOffset = _this$props6.popupOffset
        return React__default.createElement(
          Overlay,
          {
            rootClose: true,
            placement: 'bottom',
            show: !!overlay.position,
            onHide: function onHide() {
              return _this3.setState({
                overlay: null,
              })
            },
            target: function target() {
              return overlay.target
            },
          },
          function(_ref3) {
            var props = _ref3.props
            return React__default.createElement(
              Popup$1,
              _extends({}, props, {
                popupOffset: popupOffset,
                accessors: accessors,
                getters: getters,
                selected: selected,
                components: components,
                localizer: localizer,
                position: overlay.position,
                events: overlay.events,
                slotStart: overlay.date,
                slotEnd: overlay.end,
                onSelect: _this3.handleSelectEvent,
                onDoubleClick: _this3.handleDoubleClickEvent,
              })
            )
          }
        )
      }

      _proto.measureRowLimit = function measureRowLimit() {
        this.setState({
          needLimitMeasure: false,
          rowLimit: this.slotRowRef.current.getRowLimit(),
        })
      }

      _proto.selectDates = function selectDates(slotInfo) {
        var slots = this._pendingSelection.slice()

        this._pendingSelection = []
        slots.sort(function(a, b) {
          return +a - +b
        })
        notify(this.props.onSelectSlot, {
          slots: slots,
          start: slots[0],
          end: slots[slots.length - 1],
          action: slotInfo.action,
          bounds: slotInfo.bounds,
          box: slotInfo.box,
        })
      }

      _proto.clearSelection = function clearSelection() {
        clearTimeout(this._selectTimer)
        this._pendingSelection = []
      }

      return MonthView
    })(React__default.Component)

  MonthView.propTypes = {
    events: propTypes.array.isRequired,
    date: propTypes.instanceOf(Date),
    min: propTypes.instanceOf(Date),
    max: propTypes.instanceOf(Date),
    step: propTypes.number,
    getNow: propTypes.func.isRequired,
    scrollToTime: propTypes.instanceOf(Date),
    rtl: propTypes.bool,
    width: propTypes.number,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onNavigate: propTypes.func,
    onSelectSlot: propTypes.func,
    onSelectEvent: propTypes.func,
    onDoubleClickEvent: propTypes.func,
    onShowMore: propTypes.func,
    onDrillDown: propTypes.func,
    getDrilldownView: propTypes.func.isRequired,
    popup: propTypes.bool,
    popupOffset: propTypes.oneOfType([
      propTypes.number,
      propTypes.shape({
        x: propTypes.number,
        y: propTypes.number,
      }),
    ]),
  }

  MonthView.range = function(date, _ref4) {
    var localizer = _ref4.localizer
    var start = firstVisibleDay(date, localizer)
    var end = lastVisibleDay(date, localizer)
    return {
      start: start,
      end: end,
    }
  }

  MonthView.navigate = function(date, action) {
    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -1, 'month')

      case navigate.NEXT:
        return add(date, 1, 'month')

      default:
        return date
    }
  }

  MonthView.title = function(date, _ref5) {
    var localizer = _ref5.localizer
    return localizer.format(date, 'monthHeaderFormat')
  }

  var getDstOffset = function getDstOffset(start, end) {
    return start.getTimezoneOffset() - end.getTimezoneOffset()
  }

  var getKey$1 = function getKey(min, max, step, slots) {
    return (
      '' +
      +startOf(min, 'minutes') +
      ('' + +startOf(max, 'minutes')) +
      (step + '-' + slots)
    )
  }

  function getSlotMetrics$1(_ref) {
    var start = _ref.min,
      end = _ref.max,
      step = _ref.step,
      timeslots = _ref.timeslots
    var key = getKey$1(start, end, step, timeslots) // if the start is on a DST-changing day but *after* the moment of DST
    // transition we need to add those extra minutes to our minutesFromMidnight

    var daystart = startOf(start, 'day')
    var daystartdstoffset = getDstOffset(daystart, start)
    var totalMin = 1 + diff(start, end, 'minutes') + getDstOffset(start, end)
    var minutesFromMidnight =
      diff(daystart, start, 'minutes') + daystartdstoffset
    var numGroups = Math.ceil(totalMin / (step * timeslots))
    var numSlots = numGroups * timeslots
    var groups = new Array(numGroups)
    var slots = new Array(numSlots) // Each slot date is created from "zero", instead of adding `step` to
    // the previous one, in order to avoid DST oddities

    for (var grp = 0; grp < numGroups; grp++) {
      groups[grp] = new Array(timeslots)

      for (var slot = 0; slot < timeslots; slot++) {
        var slotIdx = grp * timeslots + slot
        var minFromStart = slotIdx * step // A date with total minutes calculated from the start of the day

        slots[slotIdx] = groups[grp][slot] = new Date(
          start.getFullYear(),
          start.getMonth(),
          start.getDate(),
          0,
          minutesFromMidnight + minFromStart,
          0,
          0
        )
      }
    } // Necessary to be able to select up until the last timeslot in a day

    var lastSlotMinFromStart = slots.length * step
    slots.push(
      new Date(
        start.getFullYear(),
        start.getMonth(),
        start.getDate(),
        0,
        minutesFromMidnight + lastSlotMinFromStart,
        0,
        0
      )
    )

    function positionFromDate(date) {
      var diff$1 = diff(start, date, 'minutes') + getDstOffset(start, date)
      return Math.min(diff$1, totalMin)
    }

    return {
      groups: groups,
      update: function update(args) {
        if (getKey$1(args) !== key) return getSlotMetrics$1(args)
        return this
      },
      dateIsInGroup: function dateIsInGroup(date, groupIndex) {
        var nextGroup = groups[groupIndex + 1]
        return inRange(
          date,
          groups[groupIndex][0],
          nextGroup ? nextGroup[0] : end,
          'minutes'
        )
      },
      nextSlot: function nextSlot(slot) {
        var next = slots[Math.min(slots.indexOf(slot) + 1, slots.length - 1)] // in the case of the last slot we won't a long enough range so manually get it

        if (next === slot) next = add(slot, step, 'minutes')
        return next
      },
      closestSlotToPosition: function closestSlotToPosition(percent) {
        var slot = Math.min(
          slots.length - 1,
          Math.max(0, Math.floor(percent * numSlots))
        )
        return slots[slot]
      },
      closestSlotFromPoint: function closestSlotFromPoint(point, boundaryRect) {
        var range = Math.abs(boundaryRect.top - boundaryRect.bottom)
        return this.closestSlotToPosition((point.y - boundaryRect.top) / range)
      },
      closestSlotFromDate: function closestSlotFromDate(date, offset) {
        if (offset === void 0) {
          offset = 0
        }

        if (lt(date, start, 'minutes')) return slots[0]
        var diffMins = diff(start, date, 'minutes')
        return slots[(diffMins - (diffMins % step)) / step + offset]
      },
      startsBeforeDay: function startsBeforeDay(date) {
        return lt(date, start, 'day')
      },
      startsAfterDay: function startsAfterDay(date) {
        return gt(date, end, 'day')
      },
      startsBefore: function startsBefore(date) {
        return lt(merge(start, date), start, 'minutes')
      },
      startsAfter: function startsAfter(date) {
        return gt(merge(end, date), end, 'minutes')
      },
      getRange: function getRange(rangeStart, rangeEnd, ignoreMin, ignoreMax) {
        if (!ignoreMin) rangeStart = min(end, max(start, rangeStart))
        if (!ignoreMax) rangeEnd = min(end, max(start, rangeEnd))
        var rangeStartMin = positionFromDate(rangeStart)
        var rangeEndMin = positionFromDate(rangeEnd)
        var top =
          rangeEndMin - rangeStartMin < step && !eq(end, rangeEnd)
            ? ((rangeStartMin - step) / (step * numSlots)) * 100
            : (rangeStartMin / (step * numSlots)) * 100
        return {
          top: top,
          height: (rangeEndMin / (step * numSlots)) * 100 - top,
          start: positionFromDate(rangeStart),
          startDate: rangeStart,
          end: positionFromDate(rangeEnd),
          endDate: rangeEnd,
        }
      },
      getCurrentTimePosition: function getCurrentTimePosition(rangeStart) {
        var rangeStartMin = positionFromDate(rangeStart)
        var top = (rangeStartMin / (step * numSlots)) * 100
        return top
      },
    }
  }

  function _defineProperties(target, props) {
    for (var i = 0; i < props.length; i++) {
      var descriptor = props[i]
      descriptor.enumerable = descriptor.enumerable || false
      descriptor.configurable = true
      if ('value' in descriptor) descriptor.writable = true
      Object.defineProperty(target, descriptor.key, descriptor)
    }
  }

  function _createClass(Constructor, protoProps, staticProps) {
    if (protoProps) _defineProperties(Constructor.prototype, protoProps)
    if (staticProps) _defineProperties(Constructor, staticProps)
    return Constructor
  }

  var Event =
    /*#__PURE__*/
    (function() {
      function Event(data, _ref) {
        var accessors = _ref.accessors,
          slotMetrics = _ref.slotMetrics

        var _slotMetrics$getRange = slotMetrics.getRange(
            accessors.start(data),
            accessors.end(data)
          ),
          start = _slotMetrics$getRange.start,
          startDate = _slotMetrics$getRange.startDate,
          end = _slotMetrics$getRange.end,
          endDate = _slotMetrics$getRange.endDate,
          top = _slotMetrics$getRange.top,
          height = _slotMetrics$getRange.height

        this.start = start
        this.end = end
        this.startMs = +startDate
        this.endMs = +endDate
        this.top = top
        this.height = height
        this.data = data
      }
      /**
       * The event's width without any overlap.
       */

      _createClass(Event, [
        {
          key: '_width',
          get: function get() {
            // The container event's width is determined by the maximum number of
            // events in any of its rows.
            if (this.rows) {
              var columns =
                this.rows.reduce(
                  function(max, row) {
                    return Math.max(max, row.leaves.length + 1)
                  }, // add itself
                  0
                ) + 1 // add the container

              return 100 / columns
            }

            var availableWidth = 100 - this.container._width // The row event's width is the space left by the container, divided
            // among itself and its leaves.

            if (this.leaves) {
              return availableWidth / (this.leaves.length + 1)
            } // The leaf event's width is determined by its row's width

            return this.row._width
          },
          /**
           * The event's calculated width, possibly with extra width added for
           * overlapping effect.
           */
        },
        {
          key: 'width',
          get: function get() {
            var noOverlap = this._width
            var overlap = Math.min(100, this._width * 1.7) // Containers can always grow.

            if (this.rows) {
              return overlap
            } // Rows can grow if they have leaves.

            if (this.leaves) {
              return this.leaves.length > 0 ? overlap : noOverlap
            } // Leaves can grow unless they're the last item in a row.

            var leaves = this.row.leaves
            var index = leaves.indexOf(this)
            return index === leaves.length - 1 ? noOverlap : overlap
          },
        },
        {
          key: 'xOffset',
          get: function get() {
            // Containers have no offset.
            if (this.rows) return 0 // Rows always start where their container ends.

            if (this.leaves) return this.container._width // Leaves are spread out evenly on the space left by its row.

            var _this$row = this.row,
              leaves = _this$row.leaves,
              xOffset = _this$row.xOffset,
              _width = _this$row._width
            var index = leaves.indexOf(this) + 1
            return xOffset + index * _width
          },
        },
      ])

      return Event
    })()
  /**
   * Return true if event a and b is considered to be on the same row.
   */

  function onSameRow(a, b, minimumStartDifference) {
    return (
      // Occupies the same start slot.
      Math.abs(b.start - a.start) < minimumStartDifference || // A's start slot overlaps with b's end slot.
      (b.start > a.start && b.start < a.end)
    )
  }

  function sortByRender(events) {
    var sortedByTime = sortBy(events, [
      'startMs',
      function(e) {
        return -e.endMs
      },
    ])
    var sorted = []

    while (sortedByTime.length > 0) {
      var event = sortedByTime.shift()
      sorted.push(event)

      for (var i = 0; i < sortedByTime.length; i++) {
        var test = sortedByTime[i] // Still inside this event, look for next.

        if (event.endMs > test.startMs) continue // We've found the first event of the next event group.
        // If that event is not right next to our current event, we have to
        // move it here.

        if (i > 0) {
          var _event = sortedByTime.splice(i, 1)[0]
          sorted.push(_event)
        } // We've already found the next event group, so stop looking.

        break
      }
    }

    return sorted
  }

  function getStyledEvents(_ref2) {
    var events = _ref2.events,
      minimumStartDifference = _ref2.minimumStartDifference,
      slotMetrics = _ref2.slotMetrics,
      accessors = _ref2.accessors
    // Create proxy events and order them so that we don't have
    // to fiddle with z-indexes.
    var proxies = events.map(function(event) {
      return new Event(event, {
        slotMetrics: slotMetrics,
        accessors: accessors,
      })
    })
    var eventsInRenderOrder = sortByRender(proxies) // Group overlapping events, while keeping order.
    // Every event is always one of: container, row or leaf.
    // Containers can contain rows, and rows can contain leaves.

    var containerEvents = []

    var _loop = function _loop(i) {
      var event = eventsInRenderOrder[i] // Check if this event can go into a container event.

      var container = containerEvents.find(function(c) {
        return (
          c.end > event.start ||
          Math.abs(event.start - c.start) < minimumStartDifference
        )
      }) // Couldn't find a container — that means this event is a container.

      if (!container) {
        event.rows = []
        containerEvents.push(event)
        return 'continue'
      } // Found a container for the event.

      event.container = container // Check if the event can be placed in an existing row.
      // Start looking from behind.

      var row = null

      for (var j = container.rows.length - 1; !row && j >= 0; j--) {
        if (onSameRow(container.rows[j], event, minimumStartDifference)) {
          row = container.rows[j]
        }
      }

      if (row) {
        // Found a row, so add it.
        row.leaves.push(event)
        event.row = row
      } else {
        // Couldn't find a row – that means this event is a row.
        event.leaves = []
        container.rows.push(event)
      }
    }

    for (var i = 0; i < eventsInRenderOrder.length; i++) {
      var _ret = _loop(i)

      if (_ret === 'continue') continue
    } // Return the original events, along with their styles.

    return eventsInRenderOrder.map(function(event) {
      return {
        event: event.data,
        style: {
          top: event.top,
          height: event.height,
          width: event.width,
          xOffset: event.xOffset,
        },
      }
    })
  }

  var TimeSlotGroup =
    /*#__PURE__*/
    (function(_Component) {
      _inheritsLoose(TimeSlotGroup, _Component)

      function TimeSlotGroup() {
        return _Component.apply(this, arguments) || this
      }

      var _proto = TimeSlotGroup.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          renderSlot = _this$props.renderSlot,
          resource = _this$props.resource,
          group = _this$props.group,
          getters = _this$props.getters,
          _this$props$component = _this$props.components
        _this$props$component =
          _this$props$component === void 0 ? {} : _this$props$component
        var _this$props$component2 = _this$props$component.timeSlotWrapper,
          Wrapper =
            _this$props$component2 === void 0
              ? NoopWrapper
              : _this$props$component2
        return React__default.createElement(
          'div',
          {
            className: 'rbc-timeslot-group',
          },
          group.map(function(value, idx) {
            var slotProps = getters ? getters.slotProp(value, resource) : {}
            return React__default.createElement(
              Wrapper,
              {
                key: idx,
                value: value,
                resource: resource,
              },
              React__default.createElement(
                'div',
                _extends({}, slotProps, {
                  className: clsx('rbc-time-slot', slotProps.className),
                }),
                renderSlot && renderSlot(value, idx)
              )
            )
          })
        )
      }

      return TimeSlotGroup
    })(React.Component)
  TimeSlotGroup.propTypes = {
    renderSlot: propTypes.func,
    group: propTypes.array.isRequired,
    resource: propTypes.any,
    components: propTypes.object,
    getters: propTypes.object,
  }

  /* eslint-disable react/prop-types */

  function TimeGridEvent(props) {
    var _extends2

    var style = props.style,
      className = props.className,
      event = props.event,
      accessors = props.accessors,
      rtl = props.rtl,
      selected = props.selected,
      label = props.label,
      continuesEarlier = props.continuesEarlier,
      continuesLater = props.continuesLater,
      getters = props.getters,
      onClick = props.onClick,
      onDoubleClick = props.onDoubleClick,
      _props$components = props.components,
      Event = _props$components.event,
      EventWrapper = _props$components.eventWrapper
    var title = accessors.title(event)
    var tooltip = accessors.tooltip(event)
    var end = accessors.end(event)
    var start = accessors.start(event)
    var userProps = getters.eventProp(event, start, end, selected)
    var height = style.height,
      top = style.top,
      width = style.width,
      xOffset = style.xOffset
    var inner = [
      React__default.createElement(
        'div',
        {
          key: '1',
          className: 'rbc-event-label',
        },
        label
      ),
      React__default.createElement(
        'div',
        {
          key: '2',
          className: 'rbc-event-content',
        },
        Event
          ? React__default.createElement(Event, {
              event: event,
              title: title,
            })
          : title
      ),
    ]
    return React__default.createElement(
      EventWrapper,
      _extends(
        {
          type: 'time',
        },
        props
      ),
      React__default.createElement(
        'div',
        {
          onClick: onClick,
          onDoubleClick: onDoubleClick,
          style: _extends(
            {},
            userProps.style,
            ((_extends2 = {
              top: top + '%',
              height: height + '%',
            }),
            (_extends2[rtl ? 'right' : 'left'] = Math.max(0, xOffset) + '%'),
            (_extends2.width = width + '%'),
            _extends2)
          ),
          title: tooltip
            ? (typeof label === 'string' ? label + ': ' : '') + tooltip
            : undefined,
          className: clsx('rbc-event', className, userProps.className, {
            'rbc-selected': selected,
            'rbc-event-continues-earlier': continuesEarlier,
            'rbc-event-continues-later': continuesLater,
          }),
        },
        inner
      )
    )
  }

  var DayColumn =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(DayColumn, _React$Component)

      function DayColumn() {
        var _this

        for (
          var _len = arguments.length, _args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          _args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(_args)) ||
          this
        _this.state = {
          selecting: false,
          timeIndicatorPosition: null,
        }
        _this.intervalTriggered = false

        _this.renderEvents = function() {
          var _this$props = _this.props,
            events = _this$props.events,
            rtl = _this$props.rtl,
            selected = _this$props.selected,
            accessors = _this$props.accessors,
            localizer = _this$props.localizer,
            getters = _this$props.getters,
            components = _this$props.components,
            step = _this$props.step,
            timeslots = _this$props.timeslots

          var _assertThisInitialize = _assertThisInitialized(_this),
            slotMetrics = _assertThisInitialize.slotMetrics

          var messages = localizer.messages
          var styledEvents = getStyledEvents({
            events: events,
            accessors: accessors,
            slotMetrics: slotMetrics,
            minimumStartDifference: Math.ceil((step * timeslots) / 2),
          })
          return styledEvents.map(function(_ref, idx) {
            var event = _ref.event,
              style = _ref.style
            var end = accessors.end(event)
            var start = accessors.start(event)
            var format = 'eventTimeRangeFormat'
            var label
            var startsBeforeDay = slotMetrics.startsBeforeDay(start)
            var startsAfterDay = slotMetrics.startsAfterDay(end)
            if (startsBeforeDay) format = 'eventTimeRangeEndFormat'
            else if (startsAfterDay) format = 'eventTimeRangeStartFormat'
            if (startsBeforeDay && startsAfterDay) label = messages.allDay
            else
              label = localizer.format(
                {
                  start: start,
                  end: end,
                },
                format
              )
            var continuesEarlier =
              startsBeforeDay || slotMetrics.startsBefore(start)
            var continuesLater = startsAfterDay || slotMetrics.startsAfter(end)
            return React__default.createElement(TimeGridEvent, {
              style: style,
              event: event,
              label: label,
              key: 'evt_' + idx,
              getters: getters,
              rtl: rtl,
              components: components,
              continuesEarlier: continuesEarlier,
              continuesLater: continuesLater,
              accessors: accessors,
              selected: isSelected(event, selected),
              onClick: function onClick(e) {
                return _this._select(event, e)
              },
              onDoubleClick: function onDoubleClick(e) {
                return _this._doubleClick(event, e)
              },
            })
          })
        }

        _this._selectable = function() {
          var node = ReactDOM.findDOMNode(_assertThisInitialized(_this))
          var selector = (_this._selector = new Selection(
            function() {
              return ReactDOM.findDOMNode(_assertThisInitialized(_this))
            },
            {
              longPressThreshold: _this.props.longPressThreshold,
            }
          ))

          var maybeSelect = function maybeSelect(box) {
            var onSelecting = _this.props.onSelecting
            var current = _this.state || {}
            var state = selectionState(box)
            var start = state.startDate,
              end = state.endDate

            if (onSelecting) {
              if (
                (eq(current.startDate, start, 'minutes') &&
                  eq(current.endDate, end, 'minutes')) ||
                onSelecting({
                  start: start,
                  end: end,
                }) === false
              )
                return
            }

            if (
              _this.state.start !== state.start ||
              _this.state.end !== state.end ||
              _this.state.selecting !== state.selecting
            ) {
              _this.setState(state)
            }
          }

          var selectionState = function selectionState(point) {
            var currentSlot = _this.slotMetrics.closestSlotFromPoint(
              point,
              getBoundsForNode(node)
            )

            if (!_this.state.selecting) {
              _this._initialSlot = currentSlot
            }

            var initialSlot = _this._initialSlot

            if (lte(initialSlot, currentSlot)) {
              currentSlot = _this.slotMetrics.nextSlot(currentSlot)
            } else if (gt(initialSlot, currentSlot)) {
              initialSlot = _this.slotMetrics.nextSlot(initialSlot)
            }

            var selectRange = _this.slotMetrics.getRange(
              min(initialSlot, currentSlot),
              max(initialSlot, currentSlot)
            )

            return _extends({}, selectRange, {
              selecting: true,
              top: selectRange.top + '%',
              height: selectRange.height + '%',
            })
          }

          var selectorClicksHandler = function selectorClicksHandler(
            box,
            actionType
          ) {
            if (
              !isEvent(ReactDOM.findDOMNode(_assertThisInitialized(_this)), box)
            ) {
              var _selectionState = selectionState(box),
                startDate = _selectionState.startDate,
                endDate = _selectionState.endDate

              _this._selectSlot({
                startDate: startDate,
                endDate: endDate,
                action: actionType,
                box: box,
              })
            }

            _this.setState({
              selecting: false,
            })
          }

          selector.on('selecting', maybeSelect)
          selector.on('selectStart', maybeSelect)
          selector.on('beforeSelect', function(box) {
            if (_this.props.selectable !== 'ignoreEvents') return
            return !isEvent(
              ReactDOM.findDOMNode(_assertThisInitialized(_this)),
              box
            )
          })
          selector.on('click', function(box) {
            return selectorClicksHandler(box, 'click')
          })
          selector.on('doubleClick', function(box) {
            return selectorClicksHandler(box, 'doubleClick')
          })
          selector.on('select', function(bounds) {
            if (_this.state.selecting) {
              _this._selectSlot(
                _extends({}, _this.state, {
                  action: 'select',
                  bounds: bounds,
                })
              )

              _this.setState({
                selecting: false,
              })
            }
          })
          selector.on('reset', function() {
            if (_this.state.selecting) {
              _this.setState({
                selecting: false,
              })
            }
          })
        }

        _this._teardownSelectable = function() {
          if (!_this._selector) return

          _this._selector.teardown()

          _this._selector = null
        }

        _this._selectSlot = function(_ref2) {
          var startDate = _ref2.startDate,
            endDate = _ref2.endDate,
            action = _ref2.action,
            bounds = _ref2.bounds,
            box = _ref2.box
          var current = startDate,
            slots = []

          while (lte(current, endDate)) {
            slots.push(current)
            current = add(current, _this.props.step, 'minutes')
          }

          notify(_this.props.onSelectSlot, {
            slots: slots,
            start: startDate,
            end: endDate,
            resourceId: _this.props.resource,
            action: action,
            bounds: bounds,
            box: box,
          })
        }

        _this._select = function() {
          for (
            var _len2 = arguments.length, args = new Array(_len2), _key2 = 0;
            _key2 < _len2;
            _key2++
          ) {
            args[_key2] = arguments[_key2]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this._doubleClick = function() {
          for (
            var _len3 = arguments.length, args = new Array(_len3), _key3 = 0;
            _key3 < _len3;
            _key3++
          ) {
            args[_key3] = arguments[_key3]
          }

          notify(_this.props.onDoubleClickEvent, args)
        }

        _this.slotMetrics = getSlotMetrics$1(_this.props)
        return _this
      }

      var _proto = DayColumn.prototype

      _proto.componentDidMount = function componentDidMount() {
        this.props.selectable && this._selectable()

        if (this.props.isNow) {
          this.setTimeIndicatorPositionUpdateInterval()
        }
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        this._teardownSelectable()

        this.clearTimeIndicatorInterval()
      }

      _proto.componentWillReceiveProps = function componentWillReceiveProps(
        nextProps
      ) {
        if (nextProps.selectable && !this.props.selectable) this._selectable()
        if (!nextProps.selectable && this.props.selectable)
          this._teardownSelectable()
        this.slotMetrics = this.slotMetrics.update(nextProps)
      }

      _proto.componentDidUpdate = function componentDidUpdate(
        prevProps,
        prevState
      ) {
        var getNowChanged = !eq(
          prevProps.getNow(),
          this.props.getNow(),
          'minutes'
        )

        if (prevProps.isNow !== this.props.isNow || getNowChanged) {
          this.clearTimeIndicatorInterval()

          if (this.props.isNow) {
            var tail =
              !getNowChanged &&
              eq(prevProps.date, this.props.date, 'minutes') &&
              prevState.timeIndicatorPosition ===
                this.state.timeIndicatorPosition
            this.setTimeIndicatorPositionUpdateInterval(tail)
          }
        } else if (
          this.props.isNow &&
          (!eq(prevProps.min, this.props.min, 'minutes') ||
            !eq(prevProps.max, this.props.max, 'minutes'))
        ) {
          this.positionTimeIndicator()
        }
      }

      /**
       * @param tail {Boolean} - whether `positionTimeIndicator` call should be
       *   deferred or called upon setting interval (`true` - if deferred);
       */
      _proto.setTimeIndicatorPositionUpdateInterval = function setTimeIndicatorPositionUpdateInterval(
        tail
      ) {
        var _this2 = this

        if (tail === void 0) {
          tail = false
        }

        if (!this.intervalTriggered && !tail) {
          this.positionTimeIndicator()
        }

        this._timeIndicatorTimeout = window.setTimeout(function() {
          _this2.intervalTriggered = true

          _this2.positionTimeIndicator()

          _this2.setTimeIndicatorPositionUpdateInterval()
        }, 60000)
      }

      _proto.clearTimeIndicatorInterval = function clearTimeIndicatorInterval() {
        this.intervalTriggered = false
        window.clearTimeout(this._timeIndicatorTimeout)
      }

      _proto.positionTimeIndicator = function positionTimeIndicator() {
        var _this$props2 = this.props,
          min = _this$props2.min,
          max = _this$props2.max,
          getNow = _this$props2.getNow
        var current = getNow()

        if (current >= min && current <= max) {
          var top = this.slotMetrics.getCurrentTimePosition(current)
          this.setState({
            timeIndicatorPosition: top,
          })
        } else {
          this.clearTimeIndicatorInterval()
        }
      }

      _proto.render = function render() {
        var _this$props3 = this.props,
          max = _this$props3.max,
          rtl = _this$props3.rtl,
          isNow = _this$props3.isNow,
          resource = _this$props3.resource,
          accessors = _this$props3.accessors,
          localizer = _this$props3.localizer,
          _this$props3$getters = _this$props3.getters,
          dayProp = _this$props3$getters.dayProp,
          getters = _objectWithoutPropertiesLoose(_this$props3$getters, [
            'dayProp',
          ]),
          _this$props3$componen = _this$props3.components,
          EventContainer = _this$props3$componen.eventContainerWrapper,
          components = _objectWithoutPropertiesLoose(_this$props3$componen, [
            'eventContainerWrapper',
          ])

        var slotMetrics = this.slotMetrics
        var _this$state = this.state,
          selecting = _this$state.selecting,
          top = _this$state.top,
          height = _this$state.height,
          startDate = _this$state.startDate,
          endDate = _this$state.endDate
        var selectDates = {
          start: startDate,
          end: endDate,
        }

        var _dayProp = dayProp(max),
          className = _dayProp.className,
          style = _dayProp.style

        return React__default.createElement(
          'div',
          {
            style: style,
            className: clsx(
              className,
              'rbc-day-slot',
              'rbc-time-column',
              isNow && 'rbc-now',
              isNow && 'rbc-today', // WHY
              selecting && 'rbc-slot-selecting'
            ),
          },
          slotMetrics.groups.map(function(grp, idx) {
            return React__default.createElement(TimeSlotGroup, {
              key: idx,
              group: grp,
              resource: resource,
              getters: getters,
              components: components,
            })
          }),
          React__default.createElement(
            EventContainer,
            {
              localizer: localizer,
              resource: resource,
              accessors: accessors,
              getters: getters,
              components: components,
              slotMetrics: slotMetrics,
            },
            React__default.createElement(
              'div',
              {
                className: clsx('rbc-events-container', rtl && 'rtl'),
              },
              this.renderEvents()
            )
          ),
          selecting &&
            React__default.createElement(
              'div',
              {
                className: 'rbc-slot-selection',
                style: {
                  top: top,
                  height: height,
                },
              },
              React__default.createElement(
                'span',
                null,
                localizer.format(selectDates, 'selectRangeFormat')
              )
            ),
          isNow &&
            React__default.createElement('div', {
              className: 'rbc-current-time-indicator',
              style: {
                top: this.state.timeIndicatorPosition + '%',
              },
            })
        )
      }

      return DayColumn
    })(React__default.Component)

  DayColumn.propTypes = {
    events: propTypes.array.isRequired,
    step: propTypes.number.isRequired,
    date: propTypes.instanceOf(Date).isRequired,
    min: propTypes.instanceOf(Date).isRequired,
    max: propTypes.instanceOf(Date).isRequired,
    getNow: propTypes.func.isRequired,
    isNow: propTypes.bool,
    rtl: propTypes.bool,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    showMultiDayTimes: propTypes.bool,
    culture: propTypes.string,
    timeslots: propTypes.number,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    eventOffset: propTypes.number,
    longPressThreshold: propTypes.number,
    onSelecting: propTypes.func,
    onSelectSlot: propTypes.func.isRequired,
    onSelectEvent: propTypes.func.isRequired,
    onDoubleClickEvent: propTypes.func.isRequired,
    className: propTypes.string,
    dragThroughEvents: propTypes.bool,
    resource: propTypes.any,
  }
  DayColumn.defaultProps = {
    dragThroughEvents: true,
    timeslots: 2,
  }

  var TimeGutter =
    /*#__PURE__*/
    (function(_Component) {
      _inheritsLoose(TimeGutter, _Component)

      function TimeGutter() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this = _Component.call.apply(_Component, [this].concat(args)) || this

        _this.renderSlot = function(value, idx) {
          if (idx !== 0) return null
          var _this$props = _this.props,
            localizer = _this$props.localizer,
            getNow = _this$props.getNow

          var isNow = _this.slotMetrics.dateIsInGroup(getNow(), idx)

          return React__default.createElement(
            'span',
            {
              className: clsx('rbc-label', isNow && 'rbc-now'),
            },
            localizer.format(value, 'timeGutterFormat')
          )
        }

        var _this$props2 = _this.props,
          min = _this$props2.min,
          max = _this$props2.max,
          timeslots = _this$props2.timeslots,
          step = _this$props2.step
        _this.slotMetrics = getSlotMetrics$1({
          min: min,
          max: max,
          timeslots: timeslots,
          step: step,
        })
        return _this
      }

      var _proto = TimeGutter.prototype

      _proto.componentWillReceiveProps = function componentWillReceiveProps(
        nextProps
      ) {
        var min = nextProps.min,
          max = nextProps.max,
          timeslots = nextProps.timeslots,
          step = nextProps.step
        this.slotMetrics = this.slotMetrics.update({
          min: min,
          max: max,
          timeslots: timeslots,
          step: step,
        })
      }

      _proto.render = function render() {
        var _this2 = this

        var _this$props3 = this.props,
          resource = _this$props3.resource,
          components = _this$props3.components
        return React__default.createElement(
          'div',
          {
            className: 'rbc-time-gutter rbc-time-column',
          },
          this.slotMetrics.groups.map(function(grp, idx) {
            return React__default.createElement(TimeSlotGroup, {
              key: idx,
              group: grp,
              resource: resource,
              components: components,
              renderSlot: _this2.renderSlot,
            })
          })
        )
      }

      return TimeGutter
    })(React.Component)
  TimeGutter.propTypes = {
    min: propTypes.instanceOf(Date).isRequired,
    max: propTypes.instanceOf(Date).isRequired,
    timeslots: propTypes.number.isRequired,
    step: propTypes.number.isRequired,
    getNow: propTypes.func.isRequired,
    components: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    resource: propTypes.string,
  }

  function getWidth(node, client) {
    var win = isWindow(node)
    return win ? win.innerWidth : client ? node.clientWidth : offset(node).width
  }

  var size$1
  function scrollbarSize(recalc) {
    if ((!size$1 && size$1 !== 0) || recalc) {
      if (canUseDOM) {
        var scrollDiv = document.createElement('div')
        scrollDiv.style.position = 'absolute'
        scrollDiv.style.top = '-9999px'
        scrollDiv.style.width = '50px'
        scrollDiv.style.height = '50px'
        scrollDiv.style.overflow = 'scroll'
        document.body.appendChild(scrollDiv)
        size$1 = scrollDiv.offsetWidth - scrollDiv.clientWidth
        document.body.removeChild(scrollDiv)
      }
    }

    return size$1
  }

  var ResourceHeader = function ResourceHeader(_ref) {
    var label = _ref.label
    return React__default.createElement(React__default.Fragment, null, label)
  }

  ResourceHeader.propTypes = {
    label: propTypes.node,
    index: propTypes.number,
    resource: propTypes.object,
  }

  var TimeGridHeader =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(TimeGridHeader, _React$Component)

      function TimeGridHeader() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(args)) ||
          this

        _this.handleHeaderClick = function(date, view, e) {
          e.preventDefault()
          notify(_this.props.onDrillDown, [date, view])
        }

        _this.renderRow = function(resource) {
          var _this$props = _this.props,
            events = _this$props.events,
            rtl = _this$props.rtl,
            selectable = _this$props.selectable,
            getNow = _this$props.getNow,
            range = _this$props.range,
            getters = _this$props.getters,
            localizer = _this$props.localizer,
            accessors = _this$props.accessors,
            components = _this$props.components
          var resourceId = accessors.resourceId(resource)
          var eventsToDisplay = resource
            ? events.filter(function(event) {
                return accessors.resource(event) === resourceId
              })
            : events
          return React__default.createElement(DateContentRow, {
            isAllDay: true,
            rtl: rtl,
            getNow: getNow,
            minRows: 2,
            range: range,
            events: eventsToDisplay,
            resourceId: resourceId,
            className: 'rbc-allday-cell',
            selectable: selectable,
            selected: _this.props.selected,
            components: components,
            accessors: accessors,
            getters: getters,
            localizer: localizer,
            onSelect: _this.props.onSelectEvent,
            onDoubleClick: _this.props.onDoubleClickEvent,
            onSelectSlot: _this.props.onSelectSlot,
            longPressThreshold: _this.props.longPressThreshold,
          })
        }

        return _this
      }

      var _proto = TimeGridHeader.prototype

      _proto.renderHeaderCells = function renderHeaderCells(range) {
        var _this2 = this

        var _this$props2 = this.props,
          localizer = _this$props2.localizer,
          getDrilldownView = _this$props2.getDrilldownView,
          getNow = _this$props2.getNow,
          dayProp = _this$props2.getters.dayProp,
          _this$props2$componen = _this$props2.components.header,
          HeaderComponent =
            _this$props2$componen === void 0 ? Header : _this$props2$componen
        var today = getNow()
        return range.map(function(date, i) {
          var drilldownView = getDrilldownView(date)
          var label = localizer.format(date, 'dayFormat')

          var _dayProp = dayProp(date),
            className = _dayProp.className,
            style = _dayProp.style

          var header = React__default.createElement(HeaderComponent, {
            date: date,
            label: label,
            localizer: localizer,
          })
          return React__default.createElement(
            'div',
            {
              key: i,
              style: style,
              className: clsx(
                'rbc-header',
                className,
                eq(date, today, 'day') && 'rbc-today'
              ),
            },
            drilldownView
              ? React__default.createElement(
                  'a',
                  {
                    href: '#',
                    onClick: function onClick(e) {
                      return _this2.handleHeaderClick(date, drilldownView, e)
                    },
                  },
                  header
                )
              : React__default.createElement('span', null, header)
          )
        })
      }

      _proto.render = function render() {
        var _this3 = this

        var _this$props3 = this.props,
          width = _this$props3.width,
          rtl = _this$props3.rtl,
          resources = _this$props3.resources,
          range = _this$props3.range,
          events = _this$props3.events,
          getNow = _this$props3.getNow,
          accessors = _this$props3.accessors,
          selectable = _this$props3.selectable,
          components = _this$props3.components,
          getters = _this$props3.getters,
          scrollRef = _this$props3.scrollRef,
          localizer = _this$props3.localizer,
          isOverflowing = _this$props3.isOverflowing,
          _this$props3$componen = _this$props3.components,
          TimeGutterHeader = _this$props3$componen.timeGutterHeader,
          _this$props3$componen2 = _this$props3$componen.resourceHeader,
          ResourceHeaderComponent =
            _this$props3$componen2 === void 0
              ? ResourceHeader
              : _this$props3$componen2
        var style = {}

        if (isOverflowing) {
          style[rtl ? 'marginLeft' : 'marginRight'] = scrollbarSize() + 'px'
        }

        var groupedEvents = resources.groupEvents(events)
        return React__default.createElement(
          'div',
          {
            style: style,
            ref: scrollRef,
            className: clsx(
              'rbc-time-header',
              isOverflowing && 'rbc-overflowing'
            ),
          },
          React__default.createElement(
            'div',
            {
              className: 'rbc-label rbc-time-header-gutter',
              style: {
                width: width,
                minWidth: width,
                maxWidth: width,
              },
            },
            TimeGutterHeader &&
              React__default.createElement(TimeGutterHeader, null)
          ),
          resources.map(function(_ref, idx) {
            var id = _ref[0],
              resource = _ref[1]
            return React__default.createElement(
              'div',
              {
                className: 'rbc-time-header-content',
                key: id || idx,
              },
              resource &&
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-row rbc-row-resource',
                    key: 'resource_' + idx,
                  },
                  React__default.createElement(
                    'div',
                    {
                      className: 'rbc-header',
                    },
                    React__default.createElement(ResourceHeaderComponent, {
                      index: idx,
                      label: accessors.resourceTitle(resource),
                      resource: resource,
                    })
                  )
                ),
              React__default.createElement(
                'div',
                {
                  className:
                    'rbc-row rbc-time-header-cell' +
                    (range.length <= 1
                      ? ' rbc-time-header-cell-single-day'
                      : ''),
                },
                _this3.renderHeaderCells(range)
              ),
              React__default.createElement(DateContentRow, {
                isAllDay: true,
                rtl: rtl,
                getNow: getNow,
                minRows: 2,
                range: range,
                events: groupedEvents.get(id) || [],
                resourceId: resource && id,
                className: 'rbc-allday-cell',
                selectable: selectable,
                selected: _this3.props.selected,
                components: components,
                accessors: accessors,
                getters: getters,
                localizer: localizer,
                onSelect: _this3.props.onSelectEvent,
                onDoubleClick: _this3.props.onDoubleClickEvent,
                onSelectSlot: _this3.props.onSelectSlot,
                longPressThreshold: _this3.props.longPressThreshold,
              })
            )
          })
        )
      }

      return TimeGridHeader
    })(React__default.Component)

  TimeGridHeader.propTypes = {
    range: propTypes.array.isRequired,
    events: propTypes.array.isRequired,
    resources: propTypes.object,
    getNow: propTypes.func.isRequired,
    isOverflowing: propTypes.bool,
    rtl: propTypes.bool,
    width: propTypes.number,
    localizer: propTypes.object.isRequired,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onSelectSlot: propTypes.func,
    onSelectEvent: propTypes.func,
    onDoubleClickEvent: propTypes.func,
    onDrillDown: propTypes.func,
    getDrilldownView: propTypes.func.isRequired,
    scrollRef: propTypes.any,
  }

  var NONE = {}
  function Resources(resources, accessors) {
    return {
      map: function map(fn) {
        if (!resources) return [fn([NONE, null], 0)]
        return resources.map(function(resource, idx) {
          return fn([accessors.resourceId(resource), resource], idx)
        })
      },
      groupEvents: function groupEvents(events) {
        var eventsByResource = new Map()

        if (!resources) {
          // Return all events if resources are not provided
          eventsByResource.set(NONE, events)
          return eventsByResource
        }

        events.forEach(function(event) {
          var id = accessors.resource(event) || NONE
          var resourceEvents = eventsByResource.get(id) || []
          resourceEvents.push(event)
          eventsByResource.set(id, resourceEvents)
        })
        return eventsByResource
      },
    }
  }

  var TimeGrid =
    /*#__PURE__*/
    (function(_Component) {
      _inheritsLoose(TimeGrid, _Component)

      function TimeGrid(props) {
        var _this

        _this = _Component.call(this, props) || this

        _this.handleScroll = function(e) {
          if (_this.scrollRef.current) {
            _this.scrollRef.current.scrollLeft = e.target.scrollLeft
          }
        }

        _this.handleResize = function() {
          cancel(_this.rafHandle)
          _this.rafHandle = request(_this.checkOverflow)
        }

        _this.gutterRef = function(ref) {
          _this.gutter = ref && ReactDOM.findDOMNode(ref)
        }

        _this.handleSelectAlldayEvent = function() {
          //cancel any pending selections so only the event click goes through.
          _this.clearSelection()

          for (
            var _len = arguments.length, args = new Array(_len), _key = 0;
            _key < _len;
            _key++
          ) {
            args[_key] = arguments[_key]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this.handleSelectAllDaySlot = function(slots, slotInfo) {
          var onSelectSlot = _this.props.onSelectSlot
          notify(onSelectSlot, {
            slots: slots,
            start: slots[0],
            end: slots[slots.length - 1],
            action: slotInfo.action,
          })
        }

        _this.checkOverflow = function() {
          if (_this._updatingOverflow) return
          var content = _this.contentRef.current
          var isOverflowing = content.scrollHeight > content.clientHeight

          if (_this.state.isOverflowing !== isOverflowing) {
            _this._updatingOverflow = true

            _this.setState(
              {
                isOverflowing: isOverflowing,
              },
              function() {
                _this._updatingOverflow = false
              }
            )
          }
        }

        _this.memoizedResources = index(function(resources, accessors) {
          return Resources(resources, accessors)
        })
        _this.state = {
          gutterWidth: undefined,
          isOverflowing: null,
        }
        _this.scrollRef = React__default.createRef()
        _this.contentRef = React__default.createRef()
        return _this
      }

      var _proto = TimeGrid.prototype

      _proto.componentWillMount = function componentWillMount() {
        this.calculateScroll()
      }

      _proto.componentDidMount = function componentDidMount() {
        this.checkOverflow()

        if (this.props.width == null) {
          this.measureGutter()
        }

        this.applyScroll()
        window.addEventListener('resize', this.handleResize)
      }

      _proto.componentWillUnmount = function componentWillUnmount() {
        window.removeEventListener('resize', this.handleResize)
        cancel(this.rafHandle)

        if (this.measureGutterAnimationFrameRequest) {
          window.cancelAnimationFrame(this.measureGutterAnimationFrameRequest)
        }
      }

      _proto.componentDidUpdate = function componentDidUpdate() {
        if (this.props.width == null) {
          this.measureGutter()
        }

        this.applyScroll() //this.checkOverflow()
      }

      _proto.componentWillReceiveProps = function componentWillReceiveProps(
        nextProps
      ) {
        var _this$props = this.props,
          range = _this$props.range,
          scrollToTime = _this$props.scrollToTime // When paginating, reset scroll

        if (
          !eq(nextProps.range[0], range[0], 'minute') ||
          !eq(nextProps.scrollToTime, scrollToTime, 'minute')
        ) {
          this.calculateScroll(nextProps)
        }
      }

      _proto.renderEvents = function renderEvents(range, events, now) {
        var _this2 = this

        var _this$props2 = this.props,
          min = _this$props2.min,
          max = _this$props2.max,
          components = _this$props2.components,
          accessors = _this$props2.accessors,
          localizer = _this$props2.localizer
        var resources = this.memoizedResources(this.props.resources, accessors)
        var groupedEvents = resources.groupEvents(events)
        return resources.map(function(_ref, i) {
          var id = _ref[0],
            resource = _ref[1]
          return range.map(function(date, jj) {
            var daysEvents = (groupedEvents.get(id) || []).filter(function(
              event
            ) {
              return inRange(
                date,
                accessors.start(event),
                accessors.end(event),
                'day'
              )
            })
            return React__default.createElement(
              DayColumn,
              _extends({}, _this2.props, {
                localizer: localizer,
                min: merge(date, min),
                max: merge(date, max),
                resource: resource && id,
                components: components,
                isNow: eq(date, now, 'day'),
                key: i + '-' + jj,
                date: date,
                events: daysEvents,
              })
            )
          })
        })
      }

      _proto.render = function render() {
        var _this$props3 = this.props,
          events = _this$props3.events,
          range = _this$props3.range,
          width = _this$props3.width,
          rtl = _this$props3.rtl,
          selected = _this$props3.selected,
          getNow = _this$props3.getNow,
          resources = _this$props3.resources,
          components = _this$props3.components,
          accessors = _this$props3.accessors,
          getters = _this$props3.getters,
          localizer = _this$props3.localizer,
          min = _this$props3.min,
          max = _this$props3.max,
          showMultiDayTimes = _this$props3.showMultiDayTimes,
          longPressThreshold = _this$props3.longPressThreshold
        width = width || this.state.gutterWidth
        var start = range[0],
          end = range[range.length - 1]
        this.slots = range.length
        var allDayEvents = [],
          rangeEvents = []
        events.forEach(function(event) {
          if (inRange$2(event, start, end, accessors)) {
            var eStart = accessors.start(event),
              eEnd = accessors.end(event)

            if (
              accessors.allDay(event) ||
              (isJustDate(eStart) && isJustDate(eEnd)) ||
              (!showMultiDayTimes && !eq(eStart, eEnd, 'day'))
            ) {
              allDayEvents.push(event)
            } else {
              rangeEvents.push(event)
            }
          }
        })
        allDayEvents.sort(function(a, b) {
          return sortEvents(a, b, accessors)
        })
        return React__default.createElement(
          'div',
          {
            className: clsx(
              'rbc-time-view',
              resources && 'rbc-time-view-resources'
            ),
          },
          React__default.createElement(TimeGridHeader, {
            range: range,
            events: allDayEvents,
            width: width,
            rtl: rtl,
            getNow: getNow,
            localizer: localizer,
            selected: selected,
            resources: this.memoizedResources(resources, accessors),
            selectable: this.props.selectable,
            accessors: accessors,
            getters: getters,
            components: components,
            scrollRef: this.scrollRef,
            isOverflowing: this.state.isOverflowing,
            longPressThreshold: longPressThreshold,
            onSelectSlot: this.handleSelectAllDaySlot,
            onSelectEvent: this.handleSelectAlldayEvent,
            onDoubleClickEvent: this.props.onDoubleClickEvent,
            onDrillDown: this.props.onDrillDown,
            getDrilldownView: this.props.getDrilldownView,
          }),
          React__default.createElement(
            'div',
            {
              ref: this.contentRef,
              className: 'rbc-time-content',
              onScroll: this.handleScroll,
            },
            React__default.createElement(TimeGutter, {
              date: start,
              ref: this.gutterRef,
              localizer: localizer,
              min: merge(start, min),
              max: merge(start, max),
              step: this.props.step,
              getNow: this.props.getNow,
              timeslots: this.props.timeslots,
              components: components,
              className: 'rbc-time-gutter',
            }),
            this.renderEvents(range, rangeEvents, getNow())
          )
        )
      }

      _proto.clearSelection = function clearSelection() {
        clearTimeout(this._selectTimer)
        this._pendingSelection = []
      }

      _proto.measureGutter = function measureGutter() {
        var _this3 = this

        if (this.measureGutterAnimationFrameRequest) {
          window.cancelAnimationFrame(this.measureGutterAnimationFrameRequest)
        }

        this.measureGutterAnimationFrameRequest = window.requestAnimationFrame(
          function() {
            var width = getWidth(_this3.gutter)

            if (width && _this3.state.gutterWidth !== width) {
              _this3.setState({
                gutterWidth: width,
              })
            }
          }
        )
      }

      _proto.applyScroll = function applyScroll() {
        if (this._scrollRatio) {
          var content = this.contentRef.current
          content.scrollTop = content.scrollHeight * this._scrollRatio // Only do this once

          this._scrollRatio = null
        }
      }

      _proto.calculateScroll = function calculateScroll(props) {
        if (props === void 0) {
          props = this.props
        }

        var _props = props,
          min = _props.min,
          max = _props.max,
          scrollToTime = _props.scrollToTime
        var diffMillis = scrollToTime - startOf(scrollToTime, 'day')
        var totalMillis = diff(max, min)
        this._scrollRatio = diffMillis / totalMillis
      }

      return TimeGrid
    })(React.Component)
  TimeGrid.propTypes = {
    events: propTypes.array.isRequired,
    resources: propTypes.array,
    step: propTypes.number,
    timeslots: propTypes.number,
    range: propTypes.arrayOf(propTypes.instanceOf(Date)),
    min: propTypes.instanceOf(Date),
    max: propTypes.instanceOf(Date),
    getNow: propTypes.func.isRequired,
    scrollToTime: propTypes.instanceOf(Date),
    showMultiDayTimes: propTypes.bool,
    rtl: propTypes.bool,
    width: propTypes.number,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
    selected: propTypes.object,
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),
    longPressThreshold: propTypes.number,
    onNavigate: propTypes.func,
    onSelectSlot: propTypes.func,
    onSelectEnd: propTypes.func,
    onSelectStart: propTypes.func,
    onSelectEvent: propTypes.func,
    onDoubleClickEvent: propTypes.func,
    onDrillDown: propTypes.func,
    getDrilldownView: propTypes.func.isRequired,
  }
  TimeGrid.defaultProps = {
    step: 30,
    timeslots: 2,
    min: startOf(new Date(), 'day'),
    max: endOf(new Date(), 'day'),
    scrollToTime: startOf(new Date(), 'day'),
  }

  var Day =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Day, _React$Component)

      function Day() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = Day.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          date = _this$props.date,
          props = _objectWithoutPropertiesLoose(_this$props, ['date'])

        var range = Day.range(date)
        return React__default.createElement(
          TimeGrid,
          _extends({}, props, {
            range: range,
            eventOffset: 10,
          })
        )
      }

      return Day
    })(React__default.Component)

  Day.propTypes = {
    date: propTypes.instanceOf(Date).isRequired,
  }

  Day.range = function(date) {
    return [startOf(date, 'day')]
  }

  Day.navigate = function(date, action) {
    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -1, 'day')

      case navigate.NEXT:
        return add(date, 1, 'day')

      default:
        return date
    }
  }

  Day.title = function(date, _ref) {
    var localizer = _ref.localizer
    return localizer.format(date, 'dayHeaderFormat')
  }

  var Week =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Week, _React$Component)

      function Week() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = Week.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          date = _this$props.date,
          props = _objectWithoutPropertiesLoose(_this$props, ['date'])

        var range = Week.range(date, this.props)
        return React__default.createElement(
          TimeGrid,
          _extends({}, props, {
            range: range,
            eventOffset: 15,
          })
        )
      }

      return Week
    })(React__default.Component)

  Week.propTypes = {
    date: propTypes.instanceOf(Date).isRequired,
  }
  Week.defaultProps = TimeGrid.defaultProps

  Week.navigate = function(date, action) {
    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -1, 'week')

      case navigate.NEXT:
        return add(date, 1, 'week')

      default:
        return date
    }
  }

  Week.range = function(date, _ref) {
    var localizer = _ref.localizer
    var firstOfWeek = localizer.startOfWeek()
    var start = startOf(date, 'week', firstOfWeek)
    var end = endOf(date, 'week', firstOfWeek)
    return range(start, end)
  }

  Week.title = function(date, _ref2) {
    var localizer = _ref2.localizer

    var _Week$range = Week.range(date, {
        localizer: localizer,
      }),
      start = _Week$range[0],
      rest = _Week$range.slice(1)

    return localizer.format(
      {
        start: start,
        end: rest.pop(),
      },
      'dayRangeHeaderFormat'
    )
  }

  function workWeekRange(date, options) {
    return Week.range(date, options).filter(function(d) {
      return [6, 0].indexOf(d.getDay()) === -1
    })
  }

  var WorkWeek =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(WorkWeek, _React$Component)

      function WorkWeek() {
        return _React$Component.apply(this, arguments) || this
      }

      var _proto = WorkWeek.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          date = _this$props.date,
          props = _objectWithoutPropertiesLoose(_this$props, ['date'])

        var range = workWeekRange(date, this.props)
        return React__default.createElement(
          TimeGrid,
          _extends({}, props, {
            range: range,
            eventOffset: 15,
          })
        )
      }

      return WorkWeek
    })(React__default.Component)

  WorkWeek.propTypes = {
    date: propTypes.instanceOf(Date).isRequired,
  }
  WorkWeek.defaultProps = TimeGrid.defaultProps
  WorkWeek.range = workWeekRange
  WorkWeek.navigate = Week.navigate

  WorkWeek.title = function(date, _ref) {
    var localizer = _ref.localizer

    var _workWeekRange = workWeekRange(date, {
        localizer: localizer,
      }),
      start = _workWeekRange[0],
      rest = _workWeekRange.slice(1)

    return localizer.format(
      {
        start: start,
        end: rest.pop(),
      },
      'dayRangeHeaderFormat'
    )
  }

  function hasClass(element, className) {
    if (element.classList)
      return !!className && element.classList.contains(className)
    return (
      (' ' + (element.className.baseVal || element.className) + ' ').indexOf(
        ' ' + className + ' '
      ) !== -1
    )
  }

  function addClass(element, className) {
    if (element.classList) element.classList.add(className)
    else if (!hasClass(element, className))
      if (typeof element.className === 'string')
        element.className = element.className + ' ' + className
      else
        element.setAttribute(
          'class',
          ((element.className && element.className.baseVal) || '') +
            ' ' +
            className
        )
  }

  function replaceClassName(origClass, classToRemove) {
    return origClass
      .replace(new RegExp('(^|\\s)' + classToRemove + '(?:\\s|$)', 'g'), '$1')
      .replace(/\s+/g, ' ')
      .replace(/^\s*|\s*$/g, '')
  }

  function removeClass(element, className) {
    if (element.classList) {
      element.classList.remove(className)
    } else if (typeof element.className === 'string') {
      element.className = replaceClassName(element.className, className)
    } else {
      element.setAttribute(
        'class',
        replaceClassName(
          (element.className && element.className.baseVal) || '',
          className
        )
      )
    }
  }

  var Agenda =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Agenda, _React$Component)

      function Agenda(props) {
        var _this

        _this = _React$Component.call(this, props) || this

        _this.renderDay = function(day, events, dayKey) {
          var _this$props = _this.props,
            selected = _this$props.selected,
            getters = _this$props.getters,
            accessors = _this$props.accessors,
            localizer = _this$props.localizer,
            _this$props$component = _this$props.components,
            Event = _this$props$component.event,
            AgendaDate = _this$props$component.date
          events = events.filter(function(e) {
            return inRange$2(
              e,
              startOf(day, 'day'),
              endOf(day, 'day'),
              accessors
            )
          })
          return events.map(function(event, idx) {
            var title = accessors.title(event)
            var end = accessors.end(event)
            var start = accessors.start(event)
            var userProps = getters.eventProp(
              event,
              start,
              end,
              isSelected(event, selected)
            )
            var dateLabel =
              idx === 0 && localizer.format(day, 'agendaDateFormat')
            var first =
              idx === 0
                ? React__default.createElement(
                    'td',
                    {
                      rowSpan: events.length,
                      className: 'rbc-agenda-date-cell',
                    },
                    AgendaDate
                      ? React__default.createElement(AgendaDate, {
                          day: day,
                          label: dateLabel,
                        })
                      : dateLabel
                  )
                : false
            return React__default.createElement(
              'tr',
              {
                key: dayKey + '_' + idx,
                className: userProps.className,
                style: userProps.style,
              },
              first,
              React__default.createElement(
                'td',
                {
                  className: 'rbc-agenda-time-cell',
                },
                _this.timeRangeLabel(day, event)
              ),
              React__default.createElement(
                'td',
                {
                  className: 'rbc-agenda-event-cell',
                },
                Event
                  ? React__default.createElement(Event, {
                      event: event,
                      title: title,
                    })
                  : title
              )
            )
          }, [])
        }

        _this.timeRangeLabel = function(day, event) {
          var _this$props2 = _this.props,
            accessors = _this$props2.accessors,
            localizer = _this$props2.localizer,
            components = _this$props2.components
          var labelClass = '',
            TimeComponent = components.time,
            label = localizer.messages.allDay
          var end = accessors.end(event)
          var start = accessors.start(event)

          if (!accessors.allDay(event)) {
            if (eq(start, end)) {
              label = localizer.format(start, 'agendaTimeFormat')
            } else if (eq(start, end, 'day')) {
              label = localizer.format(
                {
                  start: start,
                  end: end,
                },
                'agendaTimeRangeFormat'
              )
            } else if (eq(day, start, 'day')) {
              label = localizer.format(start, 'agendaTimeFormat')
            } else if (eq(day, end, 'day')) {
              label = localizer.format(end, 'agendaTimeFormat')
            }
          }

          if (gt(day, start, 'day')) labelClass = 'rbc-continues-prior'
          if (lt(day, end, 'day')) labelClass += ' rbc-continues-after'
          return React__default.createElement(
            'span',
            {
              className: labelClass.trim(),
            },
            TimeComponent
              ? React__default.createElement(TimeComponent, {
                  event: event,
                  day: day,
                  label: label,
                })
              : label
          )
        }

        _this._adjustHeader = function() {
          if (!_this.tbodyRef.current) return
          var header = _this.headerRef.current
          var firstRow = _this.tbodyRef.current.firstChild
          if (!firstRow) return
          var isOverflowing =
            _this.contentRef.current.scrollHeight >
            _this.contentRef.current.clientHeight
          var widths = _this._widths || []
          _this._widths = [
            getWidth(firstRow.children[0]),
            getWidth(firstRow.children[1]),
          ]

          if (
            widths[0] !== _this._widths[0] ||
            widths[1] !== _this._widths[1]
          ) {
            _this.dateColRef.current.style.width = _this._widths[0] + 'px'
            _this.timeColRef.current.style.width = _this._widths[1] + 'px'
          }

          if (isOverflowing) {
            addClass(header, 'rbc-header-overflowing')
            header.style.marginRight = scrollbarSize() + 'px'
          } else {
            removeClass(header, 'rbc-header-overflowing')
          }
        }

        _this.headerRef = React__default.createRef()
        _this.dateColRef = React__default.createRef()
        _this.timeColRef = React__default.createRef()
        _this.contentRef = React__default.createRef()
        _this.tbodyRef = React__default.createRef()
        return _this
      }

      var _proto = Agenda.prototype

      _proto.componentDidMount = function componentDidMount() {
        this._adjustHeader()
      }

      _proto.componentDidUpdate = function componentDidUpdate() {
        this._adjustHeader()
      }

      _proto.render = function render() {
        var _this2 = this

        var _this$props3 = this.props,
          length = _this$props3.length,
          date = _this$props3.date,
          events = _this$props3.events,
          accessors = _this$props3.accessors,
          localizer = _this$props3.localizer
        var messages = localizer.messages
        var end = add(date, length, 'day')
        var range$1 = range(date, end, 'day')
        events = events.filter(function(event) {
          return inRange$2(event, date, end, accessors)
        })
        events.sort(function(a, b) {
          return +accessors.start(a) - +accessors.start(b)
        })
        return React__default.createElement(
          'div',
          {
            className: 'rbc-agenda-view',
          },
          events.length !== 0
            ? React__default.createElement(
                React__default.Fragment,
                null,
                React__default.createElement(
                  'table',
                  {
                    ref: this.headerRef,
                    className: 'rbc-agenda-table',
                  },
                  React__default.createElement(
                    'thead',
                    null,
                    React__default.createElement(
                      'tr',
                      null,
                      React__default.createElement(
                        'th',
                        {
                          className: 'rbc-header',
                          ref: this.dateColRef,
                        },
                        messages.date
                      ),
                      React__default.createElement(
                        'th',
                        {
                          className: 'rbc-header',
                          ref: this.timeColRef,
                        },
                        messages.time
                      ),
                      React__default.createElement(
                        'th',
                        {
                          className: 'rbc-header',
                        },
                        messages.event
                      )
                    )
                  )
                ),
                React__default.createElement(
                  'div',
                  {
                    className: 'rbc-agenda-content',
                    ref: this.contentRef,
                  },
                  React__default.createElement(
                    'table',
                    {
                      className: 'rbc-agenda-table',
                    },
                    React__default.createElement(
                      'tbody',
                      {
                        ref: this.tbodyRef,
                      },
                      range$1.map(function(day, idx) {
                        return _this2.renderDay(day, events, idx)
                      })
                    )
                  )
                )
              )
            : React__default.createElement(
                'span',
                {
                  className: 'rbc-agenda-empty',
                },
                messages.noEventsInRange
              )
        )
      }

      return Agenda
    })(React__default.Component)

  Agenda.propTypes = {
    events: propTypes.array,
    date: propTypes.instanceOf(Date),
    length: propTypes.number.isRequired,
    selected: propTypes.object,
    accessors: propTypes.object.isRequired,
    components: propTypes.object.isRequired,
    getters: propTypes.object.isRequired,
    localizer: propTypes.object.isRequired,
  }
  Agenda.defaultProps = {
    length: 30,
  }

  Agenda.range = function(start, _ref) {
    var _ref$length = _ref.length,
      length = _ref$length === void 0 ? Agenda.defaultProps.length : _ref$length
    var end = add(start, length, 'day')
    return {
      start: start,
      end: end,
    }
  }

  Agenda.navigate = function(date, action, _ref2) {
    var _ref2$length = _ref2.length,
      length =
        _ref2$length === void 0 ? Agenda.defaultProps.length : _ref2$length

    switch (action) {
      case navigate.PREVIOUS:
        return add(date, -length, 'day')

      case navigate.NEXT:
        return add(date, length, 'day')

      default:
        return date
    }
  }

  Agenda.title = function(start, _ref3) {
    var _ref3$length = _ref3.length,
      length =
        _ref3$length === void 0 ? Agenda.defaultProps.length : _ref3$length,
      localizer = _ref3.localizer
    var end = add(start, length, 'day')
    return localizer.format(
      {
        start: start,
        end: end,
      },
      'agendaHeaderFormat'
    )
  }

  var _VIEWS
  var VIEWS =
    ((_VIEWS = {}),
    (_VIEWS[views.MONTH] = MonthView),
    (_VIEWS[views.WEEK] = Week),
    (_VIEWS[views.WORK_WEEK] = WorkWeek),
    (_VIEWS[views.DAY] = Day),
    (_VIEWS[views.AGENDA] = Agenda),
    _VIEWS)

  function moveDate(View, _ref) {
    var action = _ref.action,
      date = _ref.date,
      today = _ref.today,
      props = _objectWithoutPropertiesLoose(_ref, ['action', 'date', 'today'])

    View = typeof View === 'string' ? VIEWS[View] : View

    switch (action) {
      case navigate.TODAY:
        date = today || new Date()
        break

      case navigate.DATE:
        break

      default:
        !(View && typeof View.navigate === 'function')
          ? invariant_1(
              false,
              'Calendar View components must implement a static `.navigate(date, action)` method.s'
            )
          : void 0
        date = View.navigate(date, action, props)
    }

    return date
  }

  var Toolbar =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Toolbar, _React$Component)

      function Toolbar() {
        var _this

        for (
          var _len = arguments.length, args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(args)) ||
          this

        _this.navigate = function(action) {
          _this.props.onNavigate(action)
        }

        _this.view = function(view) {
          _this.props.onView(view)
        }

        return _this
      }

      var _proto = Toolbar.prototype

      _proto.render = function render() {
        var _this$props = this.props,
          messages = _this$props.localizer.messages,
          label = _this$props.label
        return React__default.createElement(
          'div',
          {
            className: 'rbc-toolbar',
          },
          React__default.createElement(
            'span',
            {
              className: 'rbc-btn-group',
            },
            React__default.createElement(
              'button',
              {
                type: 'button',
                onClick: this.navigate.bind(null, navigate.TODAY),
              },
              messages.today
            ),
            React__default.createElement(
              'button',
              {
                type: 'button',
                onClick: this.navigate.bind(null, navigate.PREVIOUS),
                id: 'navigate-left',
                className: 'back',
              },
              React__default.createElement('i', {
                className: 'fa fa-chevron-left',
              })
            ),
            React__default.createElement(
              'button',
              {
                type: 'button',
                onClick: this.navigate.bind(null, navigate.NEXT),
                id: 'navigate-right',
                className: 'next',
              },
              React__default.createElement('i', {
                className: 'fa fa-chevron-right',
              })
            )
          ),
          React__default.createElement(
            'span',
            {
              className: 'rbc-toolbar-label',
            },
            label
          ),
          React__default.createElement(
            'span',
            {
              className: 'rbc-btn-group',
            },
            this.viewNamesGroup(messages)
          )
        )
      }

      _proto.viewNamesGroup = function viewNamesGroup(messages) {
        var _this2 = this

        var viewNames = this.props.views
        var view = this.props.view

        if (viewNames.length > 1) {
          return viewNames.map(function(name) {
            return React__default.createElement(
              'button',
              {
                type: 'button',
                key: name,
                className: clsx({
                  'rbc-active': view === name,
                }),
                onClick: _this2.view.bind(null, name),
              },
              messages[name]
            )
          })
        }
      }

      return Toolbar
    })(React__default.Component)

  Toolbar.propTypes = {
    view: propTypes.string.isRequired,
    views: propTypes.arrayOf(propTypes.string).isRequired,
    label: propTypes.node.isRequired,
    localizer: propTypes.object,
    onNavigate: propTypes.func.isRequired,
    onView: propTypes.func.isRequired,
  }

  /**
   * Retrieve via an accessor-like property
   *
   *    accessor(obj, 'name')   // => retrieves obj['name']
   *    accessor(data, func)    // => retrieves func(data)
   *    ... otherwise null
   */
  function accessor$1(data, field) {
    var value = null
    if (typeof field === 'function') value = field(data)
    else if (
      typeof field === 'string' &&
      typeof data === 'object' &&
      data != null &&
      field in data
    )
      value = data[field]
    return value
  }
  var wrapAccessor = function wrapAccessor(acc) {
    return function(data) {
      return accessor$1(data, acc)
    }
  }

  function viewNames$1(_views) {
    return !Array.isArray(_views) ? Object.keys(_views) : _views
  }

  function isValidView(view, _ref) {
    var _views = _ref.views
    var names = viewNames$1(_views)
    return names.indexOf(view) !== -1
  }
  /**
   * react-big-calendar is a full featured Calendar component for managing events and dates. It uses
   * modern `flexbox` for layout, making it super responsive and performant. Leaving most of the layout heavy lifting
   * to the browser. __note:__ The default styles use `height: 100%` which means your container must set an explicit
   * height (feel free to adjust the styles to suit your specific needs).
   *
   * Big Calendar is unopiniated about editing and moving events, preferring to let you implement it in a way that makes
   * the most sense to your app. It also tries not to be prescriptive about your event data structures, just tell it
   * how to find the start and end datetimes and you can pass it whatever you want.
   *
   * One thing to note is that, `react-big-calendar` treats event start/end dates as an _exclusive_ range.
   * which means that the event spans up to, but not including, the end date. In the case
   * of displaying events on whole days, end dates are rounded _up_ to the next day. So an
   * event ending on `Apr 8th 12:00:00 am` will not appear on the 8th, whereas one ending
   * on `Apr 8th 12:01:00 am` will. If you want _inclusive_ ranges consider providing a
   * function `endAccessor` that returns the end date + 1 day for those events that end at midnight.
   */

  var Calendar =
    /*#__PURE__*/
    (function(_React$Component) {
      _inheritsLoose(Calendar, _React$Component)

      function Calendar() {
        var _this

        for (
          var _len = arguments.length, _args = new Array(_len), _key = 0;
          _key < _len;
          _key++
        ) {
          _args[_key] = arguments[_key]
        }

        _this =
          _React$Component.call.apply(_React$Component, [this].concat(_args)) ||
          this

        _this.getViews = function() {
          var views = _this.props.views

          if (Array.isArray(views)) {
            return transform(
              views,
              function(obj, name) {
                return (obj[name] = VIEWS[name])
              },
              {}
            )
          }

          if (typeof views === 'object') {
            return mapValues(views, function(value, key) {
              if (value === true) {
                return VIEWS[key]
              }

              return value
            })
          }

          return VIEWS
        }

        _this.getView = function() {
          var views = _this.getViews()

          return views[_this.props.view]
        }

        _this.getDrilldownView = function(date) {
          var _this$props = _this.props,
            view = _this$props.view,
            drilldownView = _this$props.drilldownView,
            getDrilldownView = _this$props.getDrilldownView
          if (!getDrilldownView) return drilldownView
          return getDrilldownView(date, view, Object.keys(_this.getViews()))
        }

        _this.handleRangeChange = function(date, viewComponent, view) {
          var _this$props2 = _this.props,
            onRangeChange = _this$props2.onRangeChange,
            localizer = _this$props2.localizer

          if (onRangeChange) {
            if (viewComponent.range) {
              onRangeChange(
                viewComponent.range(date, {
                  localizer: localizer,
                }),
                view
              )
            } else {
              warning_1(true, 'onRangeChange prop not supported for this view')
            }
          }
        }

        _this.handleNavigate = function(action, newDate) {
          var _this$props3 = _this.props,
            view = _this$props3.view,
            date = _this$props3.date,
            getNow = _this$props3.getNow,
            onNavigate = _this$props3.onNavigate,
            props = _objectWithoutPropertiesLoose(_this$props3, [
              'view',
              'date',
              'getNow',
              'onNavigate',
            ])

          var ViewComponent = _this.getView()

          var today = getNow()
          date = moveDate(
            ViewComponent,
            _extends({}, props, {
              action: action,
              date: newDate || date || today,
              today: today,
            })
          )
          onNavigate(date, view, action)

          _this.handleRangeChange(date, ViewComponent)
        }

        _this.handleViewChange = function(view) {
          if (view !== _this.props.view && isValidView(view, _this.props)) {
            _this.props.onView(view)
          }

          var views = _this.getViews()

          _this.handleRangeChange(
            _this.props.date || _this.props.getNow(),
            views[view],
            view
          )
        }

        _this.handleSelectEvent = function() {
          for (
            var _len2 = arguments.length, args = new Array(_len2), _key2 = 0;
            _key2 < _len2;
            _key2++
          ) {
            args[_key2] = arguments[_key2]
          }

          notify(_this.props.onSelectEvent, args)
        }

        _this.handleDoubleClickEvent = function() {
          for (
            var _len3 = arguments.length, args = new Array(_len3), _key3 = 0;
            _key3 < _len3;
            _key3++
          ) {
            args[_key3] = arguments[_key3]
          }

          notify(_this.props.onDoubleClickEvent, args)
        }

        _this.handleSelectSlot = function(slotInfo) {
          notify(_this.props.onSelectSlot, slotInfo)
        }

        _this.handleDrillDown = function(date, view) {
          var onDrillDown = _this.props.onDrillDown

          if (onDrillDown) {
            onDrillDown(date, view, _this.drilldownView)
            return
          }

          if (view) _this.handleViewChange(view)

          _this.handleNavigate(navigate.DATE, date)
        }

        _this.state = {
          context: _this.getContext(_this.props),
        }
        return _this
      }

      var _proto = Calendar.prototype

      _proto.componentWillReceiveProps = function componentWillReceiveProps(
        nextProps
      ) {
        this.setState({
          context: this.getContext(nextProps),
        })
      }

      _proto.getContext = function getContext(_ref2) {
        var startAccessor = _ref2.startAccessor,
          endAccessor = _ref2.endAccessor,
          allDayAccessor = _ref2.allDayAccessor,
          tooltipAccessor = _ref2.tooltipAccessor,
          titleAccessor = _ref2.titleAccessor,
          resourceAccessor = _ref2.resourceAccessor,
          resourceIdAccessor = _ref2.resourceIdAccessor,
          resourceTitleAccessor = _ref2.resourceTitleAccessor,
          eventPropGetter = _ref2.eventPropGetter,
          slotPropGetter = _ref2.slotPropGetter,
          dayPropGetter = _ref2.dayPropGetter,
          view = _ref2.view,
          views = _ref2.views,
          localizer = _ref2.localizer,
          culture = _ref2.culture,
          _ref2$messages = _ref2.messages,
          messages$1 = _ref2$messages === void 0 ? {} : _ref2$messages,
          _ref2$components = _ref2.components,
          components = _ref2$components === void 0 ? {} : _ref2$components,
          _ref2$formats = _ref2.formats,
          formats = _ref2$formats === void 0 ? {} : _ref2$formats
        var names = viewNames$1(views)
        var msgs = messages(messages$1)
        return {
          viewNames: names,
          localizer: mergeWithDefaults(localizer, culture, formats, msgs),
          getters: {
            eventProp: function eventProp() {
              return (
                (eventPropGetter && eventPropGetter.apply(void 0, arguments)) ||
                {}
              )
            },
            slotProp: function slotProp() {
              return (
                (slotPropGetter && slotPropGetter.apply(void 0, arguments)) ||
                {}
              )
            },
            dayProp: function dayProp() {
              return (
                (dayPropGetter && dayPropGetter.apply(void 0, arguments)) || {}
              )
            },
          },
          components: defaults(
            components[view] || {},
            omit(components, names),
            {
              eventWrapper: NoopWrapper,
              eventContainerWrapper: NoopWrapper,
              dateCellWrapper: NoopWrapper,
              weekWrapper: NoopWrapper,
              timeSlotWrapper: NoopWrapper,
            }
          ),
          accessors: {
            start: wrapAccessor(startAccessor),
            end: wrapAccessor(endAccessor),
            allDay: wrapAccessor(allDayAccessor),
            tooltip: wrapAccessor(tooltipAccessor),
            title: wrapAccessor(titleAccessor),
            resource: wrapAccessor(resourceAccessor),
            resourceId: wrapAccessor(resourceIdAccessor),
            resourceTitle: wrapAccessor(resourceTitleAccessor),
          },
        }
      }

      _proto.render = function render() {
        var _this$props4 = this.props,
          view = _this$props4.view,
          toolbar = _this$props4.toolbar,
          events = _this$props4.events,
          style = _this$props4.style,
          className = _this$props4.className,
          elementProps = _this$props4.elementProps,
          current = _this$props4.date,
          getNow = _this$props4.getNow,
          length = _this$props4.length,
          showMultiDayTimes = _this$props4.showMultiDayTimes,
          onShowMore = _this$props4.onShowMore,
          _0 = _this$props4.components,
          _1 = _this$props4.formats,
          _2 = _this$props4.messages,
          _3 = _this$props4.culture,
          props = _objectWithoutPropertiesLoose(_this$props4, [
            'view',
            'toolbar',
            'events',
            'style',
            'className',
            'elementProps',
            'date',
            'getNow',
            'length',
            'showMultiDayTimes',
            'onShowMore',
            'components',
            'formats',
            'messages',
            'culture',
          ])

        current = current || getNow()
        var View = this.getView()
        var _this$state$context = this.state.context,
          accessors = _this$state$context.accessors,
          components = _this$state$context.components,
          getters = _this$state$context.getters,
          localizer = _this$state$context.localizer,
          viewNames = _this$state$context.viewNames
        var CalToolbar = components.toolbar || Toolbar
        var label = View.title(current, {
          localizer: localizer,
          length: length,
        })
        return React__default.createElement(
          'div',
          _extends({}, elementProps, {
            className: clsx(className, 'rbc-calendar', props.rtl && 'rbc-rtl'),
            style: style,
          }),
          toolbar &&
            React__default.createElement(CalToolbar, {
              date: current,
              view: view,
              views: viewNames,
              label: label,
              onView: this.handleViewChange,
              onNavigate: this.handleNavigate,
              localizer: localizer,
            }),
          React__default.createElement(
            View,
            _extends({}, props, {
              events: events,
              date: current,
              getNow: getNow,
              length: length,
              localizer: localizer,
              getters: getters,
              components: components,
              accessors: accessors,
              showMultiDayTimes: showMultiDayTimes,
              getDrilldownView: this.getDrilldownView,
              onNavigate: this.handleNavigate,
              onDrillDown: this.handleDrillDown,
              onSelectEvent: this.handleSelectEvent,
              onDoubleClickEvent: this.handleDoubleClickEvent,
              onSelectSlot: this.handleSelectSlot,
              onShowMore: onShowMore,
            })
          )
        )
      }
      /**
       *
       * @param date
       * @param viewComponent
       * @param {'month'|'week'|'work_week'|'day'|'agenda'} [view] - optional
       * parameter. It appears when range change on view changing. It could be handy
       * when you need to have both: range and view type at once, i.e. for manage rbc
       * state via url
       */

      return Calendar
    })(React__default.Component)

  Calendar.defaultProps = {
    elementProps: {},
    popup: false,
    toolbar: true,
    view: views.MONTH,
    views: [views.MONTH, views.WEEK, views.DAY, views.AGENDA],
    step: 30,
    length: 30,
    drilldownView: views.DAY,
    titleAccessor: 'title',
    tooltipAccessor: 'title',
    allDayAccessor: 'allDay',
    startAccessor: 'start',
    endAccessor: 'end',
    resourceAccessor: 'resourceId',
    resourceIdAccessor: 'id',
    resourceTitleAccessor: 'title',
    longPressThreshold: 250,
    getNow: function getNow() {
      return new Date()
    },
  }
  Calendar.propTypes = {
    localizer: propTypes.object.isRequired,

    /**
     * Props passed to main calendar `<div>`.
     *
     */
    elementProps: propTypes.object,

    /**
     * The current date value of the calendar. Determines the visible view range.
     * If `date` is omitted then the result of `getNow` is used; otherwise the
     * current date is used.
     *
     * @controllable onNavigate
     */
    date: propTypes.instanceOf(Date),

    /**
     * The current view of the calendar.
     *
     * @default 'month'
     * @controllable onView
     */
    view: propTypes.string,

    /**
     * The initial view set for the Calendar.
     * @type Calendar.Views ('month'|'week'|'work_week'|'day'|'agenda')
     * @default 'month'
     */
    defaultView: propTypes.string,

    /**
     * An array of event objects to display on the calendar. Events objects
     * can be any shape, as long as the Calendar knows how to retrieve the
     * following details of the event:
     *
     *  - start time
     *  - end time
     *  - title
     *  - whether its an "all day" event or not
     *  - any resource the event may be related to
     *
     * Each of these properties can be customized or generated dynamically by
     * setting the various "accessor" props. Without any configuration the default
     * event should look like:
     *
     * ```js
     * Event {
     *   title: string,
     *   start: Date,
     *   end: Date,
     *   allDay?: boolean
     *   resource?: any,
     * }
     * ```
     */
    events: propTypes.arrayOf(propTypes.object),

    /**
     * Accessor for the event title, used to display event information. Should
     * resolve to a `renderable` value.
     *
     * ```js
     * string | (event: Object) => string
     * ```
     *
     * @type {(func|string)}
     */
    titleAccessor: accessor,

    /**
     * Accessor for the event tooltip. Should
     * resolve to a `renderable` value. Removes the tooltip if null.
     *
     * ```js
     * string | (event: Object) => string
     * ```
     *
     * @type {(func|string)}
     */
    tooltipAccessor: accessor,

    /**
     * Determines whether the event should be considered an "all day" event and ignore time.
     * Must resolve to a `boolean` value.
     *
     * ```js
     * string | (event: Object) => boolean
     * ```
     *
     * @type {(func|string)}
     */
    allDayAccessor: accessor,

    /**
     * The start date/time of the event. Must resolve to a JavaScript `Date` object.
     *
     * ```js
     * string | (event: Object) => Date
     * ```
     *
     * @type {(func|string)}
     */
    startAccessor: accessor,

    /**
     * The end date/time of the event. Must resolve to a JavaScript `Date` object.
     *
     * ```js
     * string | (event: Object) => Date
     * ```
     *
     * @type {(func|string)}
     */
    endAccessor: accessor,

    /**
     * Returns the id of the `resource` that the event is a member of. This
     * id should match at least one resource in the `resources` array.
     *
     * ```js
     * string | (event: Object) => Date
     * ```
     *
     * @type {(func|string)}
     */
    resourceAccessor: accessor,

    /**
     * An array of resource objects that map events to a specific resource.
     * Resource objects, like events, can be any shape or have any properties,
     * but should be uniquly identifiable via the `resourceIdAccessor`, as
     * well as a "title" or name as provided by the `resourceTitleAccessor` prop.
     */
    resources: propTypes.arrayOf(propTypes.object),

    /**
     * Provides a unique identifier for each resource in the `resources` array
     *
     * ```js
     * string | (resource: Object) => any
     * ```
     *
     * @type {(func|string)}
     */
    resourceIdAccessor: accessor,

    /**
     * Provides a human readable name for the resource object, used in headers.
     *
     * ```js
     * string | (resource: Object) => any
     * ```
     *
     * @type {(func|string)}
     */
    resourceTitleAccessor: accessor,

    /**
     * Determines the current date/time which is highlighted in the views.
     *
     * The value affects which day is shaded and which time is shown as
     * the current time. It also affects the date used by the Today button in
     * the toolbar.
     *
     * Providing a value here can be useful when you are implementing time zones
     * using the `startAccessor` and `endAccessor` properties.
     *
     * @type {func}
     * @default () => new Date()
     */
    getNow: propTypes.func,

    /**
     * Callback fired when the `date` value changes.
     *
     * @controllable date
     */
    onNavigate: propTypes.func,

    /**
     * Callback fired when the `view` value changes.
     *
     * @controllable view
     */
    onView: propTypes.func,

    /**
     * Callback fired when date header, or the truncated events links are clicked
     *
     */
    onDrillDown: propTypes.func,

    /**
     *
     * ```js
     * (dates: Date[] | { start: Date; end: Date }, view?: 'month'|'week'|'work_week'|'day'|'agenda') => void
     * ```
     *
     * Callback fired when the visible date range changes. Returns an Array of dates
     * or an object with start and end dates for BUILTIN views. Optionally new `view`
     * will be returned when callback called after view change.
     *
     * Custom views may return something different.
     */
    onRangeChange: propTypes.func,

    /**
     * A callback fired when a date selection is made. Only fires when `selectable` is `true`.
     *
     * ```js
     * (
     *   slotInfo: {
     *     start: Date,
     *     end: Date,
     *     slots: Array<Date>,
     *     action: "select" | "click" | "doubleClick",
     *     bounds: ?{ // For "select" action
     *       x: number,
     *       y: number,
     *       top: number,
     *       right: number,
     *       left: number,
     *       bottom: number,
     *     },
     *     box: ?{ // For "click" or "doubleClick" actions
     *       clientX: number,
     *       clientY: number,
     *       x: number,
     *       y: number,
     *     },
     *   }
     * ) => any
     * ```
     */
    onSelectSlot: propTypes.func,

    /**
     * Callback fired when a calendar event is selected.
     *
     * ```js
     * (event: Object, e: SyntheticEvent) => any
     * ```
     *
     * @controllable selected
     */
    onSelectEvent: propTypes.func,

    /**
     * Callback fired when a calendar event is clicked twice.
     *
     * ```js
     * (event: Object, e: SyntheticEvent) => void
     * ```
     */
    onDoubleClickEvent: propTypes.func,

    /**
     * Callback fired when dragging a selection in the Time views.
     *
     * Returning `false` from the handler will prevent a selection.
     *
     * ```js
     * (range: { start: Date, end: Date }) => ?boolean
     * ```
     */
    onSelecting: propTypes.func,

    /**
     * Callback fired when a +{count} more is clicked
     *
     * ```js
     * (events: Object, date: Date) => any
     * ```
     */
    onShowMore: propTypes.func,

    /**
     * The selected event, if any.
     */
    selected: propTypes.object,

    /**
     * An array of built-in view names to allow the calendar to display.
     * accepts either an array of builtin view names,
     *
     * ```jsx
     * views={['month', 'day', 'agenda']}
     * ```
     * or an object hash of the view name and the component (or boolean for builtin).
     *
     * ```jsx
     * views={{
     *   month: true,
     *   week: false,
     *   myweek: WorkWeekViewComponent,
     * }}
     * ```
     *
     * Custom views can be any React component, that implements the following
     * interface:
     *
     * ```js
     * interface View {
     *   static title(date: Date, { formats: DateFormat[], culture: string?, ...props }): string
     *   static navigate(date: Date, action: 'PREV' | 'NEXT' | 'DATE'): Date
     * }
     * ```
     *
     * @type Views ('month'|'week'|'work_week'|'day'|'agenda')
     * @View
     ['month', 'week', 'day', 'agenda']
     */
    views: views$1,

    /**
     * The string name of the destination view for drill-down actions, such
     * as clicking a date header, or the truncated events links. If
     * `getDrilldownView` is also specified it will be used instead.
     *
     * Set to `null` to disable drill-down actions.
     *
     * ```js
     * <Calendar
     *   drilldownView="agenda"
     * />
     * ```
     */
    drilldownView: propTypes.string,

    /**
     * Functionally equivalent to `drilldownView`, but accepts a function
     * that can return a view name. It's useful for customizing the drill-down
     * actions depending on the target date and triggering view.
     *
     * Return `null` to disable drill-down actions.
     *
     * ```js
     * <Calendar
     *   getDrilldownView={(targetDate, currentViewName, configuredViewNames) =>
     *     if (currentViewName === 'month' && configuredViewNames.includes('week'))
     *       return 'week'
     *
     *     return null;
     *   }}
     * />
     * ```
     */
    getDrilldownView: propTypes.func,

    /**
     * Determines the end date from date prop in the agenda view
     * date prop + length (in number of days) = end date
     */
    length: propTypes.number,

    /**
     * Determines whether the toolbar is displayed
     */
    toolbar: propTypes.bool,

    /**
     * Show truncated events in an overlay when you click the "+_x_ more" link.
     */
    popup: propTypes.bool,

    /**
     * Distance in pixels, from the edges of the viewport, the "show more" overlay should be positioned.
     *
     * ```jsx
     * <Calendar popupOffset={30}/>
     * <Calendar popupOffset={{x: 30, y: 20}}/>
     * ```
     */
    popupOffset: propTypes.oneOfType([
      propTypes.number,
      propTypes.shape({
        x: propTypes.number,
        y: propTypes.number,
      }),
    ]),

    /**
     * Allows mouse selection of ranges of dates/times.
     *
     * The 'ignoreEvents' option prevents selection code from running when a
     * drag begins over an event. Useful when you want custom event click or drag
     * logic
     */
    selectable: propTypes.oneOf([true, false, 'ignoreEvents']),

    /**
     * Specifies the number of miliseconds the user must press and hold on the screen for a touch
     * to be considered a "long press." Long presses are used for time slot selection on touch
     * devices.
     *
     * @type {number}
     * @default 250
     */
    longPressThreshold: propTypes.number,

    /**
     * Determines the selectable time increments in week and day views
     */
    step: propTypes.number,

    /**
     * The number of slots per "section" in the time grid views. Adjust with `step`
     * to change the default of 1 hour long groups, with 30 minute slots.
     */
    timeslots: propTypes.number,

    /**
     *Switch the calendar to a `right-to-left` read direction.
     */
    rtl: propTypes.bool,

    /**
     * Optionally provide a function that returns an object of className or style props
     * to be applied to the the event node.
     *
     * ```js
     * (
     * 	event: Object,
     * 	start: Date,
     * 	end: Date,
     * 	isSelected: boolean
     * ) => { className?: string, style?: Object }
     * ```
     */
    eventPropGetter: propTypes.func,

    /**
     * Optionally provide a function that returns an object of className or style props
     * to be applied to the the time-slot node. Caution! Styles that change layout or
     * position may break the calendar in unexpected ways.
     *
     * ```js
     * (date: Date, resourceId: (number|string)) => { className?: string, style?: Object }
     * ```
     */
    slotPropGetter: propTypes.func,

    /**
     * Optionally provide a function that returns an object of className or style props
     * to be applied to the the day background. Caution! Styles that change layout or
     * position may break the calendar in unexpected ways.
     *
     * ```js
     * (date: Date) => { className?: string, style?: Object }
     * ```
     */
    dayPropGetter: propTypes.func,

    /**
     * Support to show multi-day events with specific start and end times in the
     * main time grid (rather than in the all day header).
     *
     * **Note: This may cause calendars with several events to look very busy in
     * the week and day views.**
     */
    showMultiDayTimes: propTypes.bool,

    /**
     * Constrains the minimum _time_ of the Day and Week views.
     */
    min: propTypes.instanceOf(Date),

    /**
     * Constrains the maximum _time_ of the Day and Week views.
     */
    max: propTypes.instanceOf(Date),

    /**
     * Determines how far down the scroll pane is initially scrolled down.
     */
    scrollToTime: propTypes.instanceOf(Date),

    /**
     * Specify a specific culture code for the Calendar.
     *
     * **Note: it's generally better to handle this globally via your i18n library.**
     */
    culture: propTypes.string,

    /**
     * Localizer specific formats, tell the Calendar how to format and display dates.
     *
     * `format` types are dependent on the configured localizer; both Moment and Globalize
     * accept strings of tokens according to their own specification, such as: `'DD mm yyyy'`.
     *
     * ```jsx
     * let formats = {
     *   dateFormat: 'dd',
     *
     *   dayFormat: (date, , localizer) =>
     *     localizer.format(date, 'DDD', culture),
     *
     *   dayRangeHeaderFormat: ({ start, end }, culture, localizer) =>
     *     localizer.format(start, { date: 'short' }, culture) + ' – ' +
     *     localizer.format(end, { date: 'short' }, culture)
     * }
     *
     * <Calendar formats={formats} />
     * ```
     *
     * All localizers accept a function of
     * the form `(date: Date, culture: ?string, localizer: Localizer) -> string`
     */
    formats: propTypes.shape({
      /**
       * Format for the day of the month heading in the Month view.
       * e.g. "01", "02", "03", etc
       */
      dateFormat: dateFormat,

      /**
       * A day of the week format for Week and Day headings,
       * e.g. "Wed 01/04"
       *
       */
      dayFormat: dateFormat,

      /**
       * Week day name format for the Month week day headings,
       * e.g: "Sun", "Mon", "Tue", etc
       *
       */
      weekdayFormat: dateFormat,

      /**
       * The timestamp cell formats in Week and Time views, e.g. "4:00 AM"
       */
      timeGutterFormat: dateFormat,

      /**
       * Toolbar header format for the Month view, e.g "2015 April"
       *
       */
      monthHeaderFormat: dateFormat,

      /**
       * Toolbar header format for the Week views, e.g. "Mar 29 - Apr 04"
       */
      dayRangeHeaderFormat: dateRangeFormat,

      /**
       * Toolbar header format for the Day view, e.g. "Wednesday Apr 01"
       */
      dayHeaderFormat: dateFormat,

      /**
       * Toolbar header format for the Agenda view, e.g. "4/1/2015 – 5/1/2015"
       */
      agendaHeaderFormat: dateRangeFormat,

      /**
       * A time range format for selecting time slots, e.g "8:00am – 2:00pm"
       */
      selectRangeFormat: dateRangeFormat,
      agendaDateFormat: dateFormat,
      agendaTimeFormat: dateFormat,
      agendaTimeRangeFormat: dateRangeFormat,

      /**
       * Time range displayed on events.
       */
      eventTimeRangeFormat: dateRangeFormat,

      /**
       * An optional event time range for events that continue onto another day
       */
      eventTimeRangeStartFormat: dateFormat,

      /**
       * An optional event time range for events that continue from another day
       */
      eventTimeRangeEndFormat: dateFormat,
    }),

    /**
     * Customize how different sections of the calendar render by providing custom Components.
     * In particular the `Event` component can be specified for the entire calendar, or you can
     * provide an individual component for each view type.
     *
     * ```jsx
     * let components = {
     *   event: MyEvent, // used by each view (Month, Day, Week)
     *   eventWrapper: MyEventWrapper,
     *   eventContainerWrapper: MyEventContainerWrapper,
     *   dateCellWrapper: MyDateCellWrapper,
     *   timeSlotWrapper: MyTimeSlotWrapper,
     *   timeGutterHeader: MyTimeGutterWrapper,
     *   toolbar: MyToolbar,
     *   agenda: {
     *   	 event: MyAgendaEvent // with the agenda view use a different component to render events
     *     time: MyAgendaTime,
     *     date: MyAgendaDate,
     *   },
     *   day: {
     *     header: MyDayHeader,
     *     event: MyDayEvent,
     *   },
     *   week: {
     *     header: MyWeekHeader,
     *     event: MyWeekEvent,
     *   },
     *   month: {
     *     header: MyMonthHeader,
     *     dateHeader: MyMonthDateHeader,
     *     event: MyMonthEvent,
     *   }
     * }
     * <Calendar components={components} />
     * ```
     */
    components: propTypes.shape({
      event: propTypes.elementType,
      eventWrapper: propTypes.elementType,
      eventContainerWrapper: propTypes.elementType,
      dateCellWrapper: propTypes.elementType,
      timeSlotWrapper: propTypes.elementType,
      timeGutterHeader: propTypes.elementType,
      resourceHeader: propTypes.elementType,
      toolbar: propTypes.elementType,
      agenda: propTypes.shape({
        date: propTypes.elementType,
        time: propTypes.elementType,
        event: propTypes.elementType,
      }),
      day: propTypes.shape({
        header: propTypes.elementType,
        event: propTypes.elementType,
      }),
      week: propTypes.shape({
        header: propTypes.elementType,
        event: propTypes.elementType,
      }),
      month: propTypes.shape({
        header: propTypes.elementType,
        dateHeader: propTypes.elementType,
        event: propTypes.elementType,
      }),
    }),

    /**
     * String messages used throughout the component, override to provide localizations
     */
    messages: propTypes.shape({
      allDay: propTypes.node,
      previous: propTypes.node,
      next: propTypes.node,
      today: propTypes.node,
      month: propTypes.node,
      week: propTypes.node,
      day: propTypes.node,
      agenda: propTypes.node,
      date: propTypes.node,
      time: propTypes.node,
      event: propTypes.node,
      noEventsInRange: propTypes.node,
      showMore: propTypes.func,
    }),
  }
  var Calendar$1 = uncontrollable(Calendar, {
    view: 'onView',
    date: 'onNavigate',
    selected: 'onSelectEvent',
  })

  var dateRangeFormat$1 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(start, 'L', culture) +
      ' – ' +
      local.format(end, 'L', culture)
    )
  }

  var timeRangeFormat = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(start, 'LT', culture) +
      ' – ' +
      local.format(end, 'LT', culture)
    )
  }

  var timeRangeStartFormat = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return local.format(start, 'LT', culture) + ' – '
  }

  var timeRangeEndFormat = function timeRangeEndFormat(_ref4, culture, local) {
    var end = _ref4.end
    return ' – ' + local.format(end, 'LT', culture)
  }

  var weekRangeFormat = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMMM DD', culture) +
      ' – ' +
      local.format(end, 'MMMM DD', culture)
    )
  }

  var formats = {
    dateFormat: 'DD',
    dayFormat: 'DD ddd',
    weekdayFormat: 'ddd',
    selectRangeFormat: timeRangeFormat,
    eventTimeRangeFormat: timeRangeFormat,
    eventTimeRangeStartFormat: timeRangeStartFormat,
    eventTimeRangeEndFormat: timeRangeEndFormat,
    timeGutterFormat: 'LT',
    monthHeaderFormat: 'MMMM YYYY',
    dayHeaderFormat: 'dddd MMM DD',
    dayRangeHeaderFormat: weekRangeFormat,
    agendaHeaderFormat: dateRangeFormat$1,
    agendaDateFormat: 'ddd MMM DD',
    agendaTimeFormat: 'LT',
    agendaTimeRangeFormat: timeRangeFormat,
  }
  function moment(moment) {
    var locale = function locale(m, c) {
      return c ? m.locale(c) : m
    }

    return new DateLocalizer({
      formats: formats,
      firstOfWeek: function firstOfWeek(culture) {
        var data = culture ? moment.localeData(culture) : moment.localeData()
        return data ? data.firstDayOfWeek() : 0
      },
      format: function format(value, _format, culture) {
        return locale(moment(value), culture).format(_format)
      },
    })
  }

  var dateRangeFormat$2 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(start, 'd', culture) +
      ' – ' +
      local.format(end, 'd', culture)
    )
  }

  var timeRangeFormat$1 = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(start, 't', culture) +
      ' – ' +
      local.format(end, 't', culture)
    )
  }

  var timeRangeStartFormat$1 = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return local.format(start, 't', culture) + ' – '
  }

  var timeRangeEndFormat$1 = function timeRangeEndFormat(
    _ref4,
    culture,
    local
  ) {
    var end = _ref4.end
    return ' – ' + local.format(end, 't', culture)
  }

  var weekRangeFormat$1 = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMM dd', culture) +
      ' – ' +
      local.format(end, 'MMM dd', culture)
    )
  }

  var formats$1 = {
    dateFormat: 'dd',
    dayFormat: 'ddd dd/MM',
    weekdayFormat: 'ddd',
    selectRangeFormat: timeRangeFormat$1,
    eventTimeRangeFormat: timeRangeFormat$1,
    eventTimeRangeStartFormat: timeRangeStartFormat$1,
    eventTimeRangeEndFormat: timeRangeEndFormat$1,
    timeGutterFormat: 't',
    monthHeaderFormat: 'Y',
    dayHeaderFormat: 'dddd MMM dd',
    dayRangeHeaderFormat: weekRangeFormat$1,
    agendaHeaderFormat: dateRangeFormat$2,
    agendaDateFormat: 'ddd MMM dd',
    agendaTimeFormat: 't',
    agendaTimeRangeFormat: timeRangeFormat$1,
  }
  function oldGlobalize(globalize) {
    function getCulture(culture) {
      return culture
        ? globalize.findClosestCulture(culture)
        : globalize.culture()
    }

    function firstOfWeek(culture) {
      culture = getCulture(culture)
      return (culture && culture.calendar.firstDay) || 0
    }

    return new DateLocalizer({
      firstOfWeek: firstOfWeek,
      formats: formats$1,
      format: function format(value, _format, culture) {
        return globalize.format(value, _format, culture)
      },
    })
  }

  var dateRangeFormat$3 = function dateRangeFormat(_ref, culture, local) {
    var start = _ref.start,
      end = _ref.end
    return (
      local.format(
        start,
        {
          date: 'short',
        },
        culture
      ) +
      ' – ' +
      local.format(
        end,
        {
          date: 'short',
        },
        culture
      )
    )
  }

  var timeRangeFormat$2 = function timeRangeFormat(_ref2, culture, local) {
    var start = _ref2.start,
      end = _ref2.end
    return (
      local.format(
        start,
        {
          time: 'short',
        },
        culture
      ) +
      ' – ' +
      local.format(
        end,
        {
          time: 'short',
        },
        culture
      )
    )
  }

  var timeRangeStartFormat$2 = function timeRangeStartFormat(
    _ref3,
    culture,
    local
  ) {
    var start = _ref3.start
    return (
      local.format(
        start,
        {
          time: 'short',
        },
        culture
      ) + ' – '
    )
  }

  var timeRangeEndFormat$2 = function timeRangeEndFormat(
    _ref4,
    culture,
    local
  ) {
    var end = _ref4.end
    return (
      ' – ' +
      local.format(
        end,
        {
          time: 'short',
        },
        culture
      )
    )
  }

  var weekRangeFormat$2 = function weekRangeFormat(_ref5, culture, local) {
    var start = _ref5.start,
      end = _ref5.end
    return (
      local.format(start, 'MMM dd', culture) +
      ' – ' +
      local.format(end, 'MMM dd', culture)
    )
  }

  var formats$2 = {
    dateFormat: 'dd',
    dayFormat: 'eee dd/MM',
    weekdayFormat: 'eee',
    selectRangeFormat: timeRangeFormat$2,
    eventTimeRangeFormat: timeRangeFormat$2,
    eventTimeRangeStartFormat: timeRangeStartFormat$2,
    eventTimeRangeEndFormat: timeRangeEndFormat$2,
    timeGutterFormat: {
      time: 'short',
    },
    monthHeaderFormat: 'MMMM yyyy',
    dayHeaderFormat: 'eeee MMM dd',
    dayRangeHeaderFormat: weekRangeFormat$2,
    agendaHeaderFormat: dateRangeFormat$3,
    agendaDateFormat: 'eee MMM dd',
    agendaTimeFormat: {
      time: 'short',
    },
    agendaTimeRangeFormat: timeRangeFormat$2,
  }
  function globalize(globalize) {
    var locale = function locale(culture) {
      return culture ? globalize(culture) : globalize
    } // return the first day of the week from the locale data. Defaults to 'world'
    // territory if no territory is derivable from CLDR.
    // Failing to use CLDR supplemental (not loaded?), revert to the original
    // method of getting first day of week.

    function firstOfWeek(culture) {
      try {
        var days = ['sun', 'mon', 'tue', 'wed', 'thu', 'fri', 'sat']
        var cldr = locale(culture).cldr
        var territory = cldr.attributes.territory
        var weekData = cldr.get('supplemental').weekData
        var firstDay = weekData.firstDay[territory || '001']
        return days.indexOf(firstDay)
      } catch (e) {
        warning_1(
          true,
          'Failed to accurately determine first day of the week.\n            Is supplemental data loaded into CLDR?'
        ) // maybe cldr supplemental is not loaded? revert to original method

        var date = new Date() //cldr-data doesn't seem to be zero based

        var localeDay = Math.max(
          parseInt(
            locale(culture).formatDate(date, {
              raw: 'e',
            }),
            10
          ) - 1,
          0
        )
        return Math.abs(date.getDay() - localeDay)
      }
    }

    if (!globalize.load) return oldGlobalize(globalize)
    return new DateLocalizer({
      firstOfWeek: firstOfWeek,
      formats: formats$2,
      format: function format(value, _format, culture) {
        _format =
          typeof _format === 'string'
            ? {
                raw: _format,
              }
            : _format
        return locale(culture).formatDate(value, _format)
      },
    })
  }

  var components = {
    eventWrapper: NoopWrapper,
    timeSlotWrapper: NoopWrapper,
    dateCellWrapper: NoopWrapper,
  }

  exports.Calendar = Calendar$1
  exports.DateLocalizer = DateLocalizer
  exports.Navigate = navigate
  exports.Views = views
  exports.components = components
  exports.globalizeLocalizer = globalize
  exports.momentLocalizer = moment
  exports.move = moveDate

  Object.defineProperty(exports, '__esModule', { value: true })
})
