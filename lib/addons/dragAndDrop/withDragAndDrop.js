'use strict'

var _interopRequireDefault = require('@babel/runtime/helpers/interopRequireDefault')

exports.__esModule = true
exports.default = withDragAndDrop

var _extends2 = _interopRequireDefault(
  require('@babel/runtime/helpers/extends')
)

var _objectWithoutPropertiesLoose2 = _interopRequireDefault(
  require('@babel/runtime/helpers/objectWithoutPropertiesLoose')
)

var _inheritsLoose2 = _interopRequireDefault(
  require('@babel/runtime/helpers/inheritsLoose')
)

var _propTypes = _interopRequireDefault(require('prop-types'))

var _react = _interopRequireDefault(require('react'))

var _clsx = _interopRequireDefault(require('clsx'))

var _propTypes2 = require('../../utils/propTypes')

var _EventWrapper = _interopRequireDefault(require('./EventWrapper'))

var _EventContainerWrapper = _interopRequireDefault(
  require('./EventContainerWrapper')
)

var _WeekWrapper = _interopRequireDefault(require('./WeekWrapper'))

var _common = require('./common')

function withDragAndDrop(Calendar) {
  var DragAndDropCalendar =
    /*#__PURE__*/
    (function(_React$Component) {
      ;(0, _inheritsLoose2.default)(DragAndDropCalendar, _React$Component)

      function DragAndDropCalendar() {
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

        _this.defaultOnDragOver = function(event) {
          event.preventDefault()
        }

        _this.handleBeginAction = function(event, action, direction) {
          var onDragStart = _this.props.onDragStart

          _this.setState({
            event: event,
            action: action,
            direction: direction,
          })

          if (onDragStart) {
            onDragStart({
              event: event,
              action: action,
              direction: direction,
            })
          }
        }

        _this.handleInteractionStart = function() {
          if (_this.state.interacting === false)
            _this.setState({
              interacting: true,
            })
        }

        _this.handleInteractionEnd = function(interactionInfo) {
          var _this$state = _this.state,
            action = _this$state.action,
            event = _this$state.event
          if (!action) return

          _this.setState({
            action: null,
            event: null,
            interacting: false,
            direction: null,
          })

          if (interactionInfo == null) return
          interactionInfo.event = event
          if (action === 'move') _this.props.onEventDrop(interactionInfo)
          if (action === 'resize') _this.props.onEventResize(interactionInfo)
        }

        var components = _this.props.components
        _this.components = (0, _common.mergeComponents)(components, {
          eventWrapper: _EventWrapper.default,
          eventContainerWrapper: _EventContainerWrapper.default,
          weekWrapper: _WeekWrapper.default,
        })
        _this.state = {
          interacting: false,
        }
        return _this
      }

      var _proto = DragAndDropCalendar.prototype

      _proto.getChildContext = function getChildContext() {
        return {
          draggable: {
            onStart: this.handleInteractionStart,
            onEnd: this.handleInteractionEnd,
            onBeginAction: this.handleBeginAction,
            onDropFromOutside: this.props.onDropFromOutside,
            dragFromOutsideItem: this.props.dragFromOutsideItem,
            draggableAccessor: this.props.draggableAccessor,
            resizableAccessor: this.props.resizableAccessor,
            dragAndDropAction: this.state,
          },
        }
      }

      _proto.render = function render() {
        var _this$props = this.props,
          selectable = _this$props.selectable,
          elementProps = _this$props.elementProps,
          props = (0, _objectWithoutPropertiesLoose2.default)(_this$props, [
            'selectable',
            'elementProps',
          ])
        var interacting = this.state.interacting
        delete props.onEventDrop
        delete props.onEventResize
        props.selectable = selectable ? 'ignoreEvents' : false
        var elementPropsWithDropFromOutside = this.props.onDropFromOutside
          ? (0, _extends2.default)({}, elementProps, {
              onDragOver: this.props.onDragOver || this.defaultOnDragOver,
            })
          : elementProps
        props.className = (0, _clsx.default)(
          props.className,
          'rbc-addons-dnd',
          !!interacting && 'rbc-addons-dnd-is-dragging'
        )
        return _react.default.createElement(
          Calendar,
          (0, _extends2.default)({}, props, {
            elementProps: elementPropsWithDropFromOutside,
            components: this.components,
          })
        )
      }

      return DragAndDropCalendar
    })(_react.default.Component)

  DragAndDropCalendar.defaultProps = {
    // TODO: pick these up from Calendar.defaultProps
    components: {},
    draggableAccessor: null,
    resizableAccessor: null,
    step: 30,
  }
  DragAndDropCalendar.contextTypes = {
    dragDropManager: _propTypes.default.object,
  }
  DragAndDropCalendar.childContextTypes = {
    draggable: _propTypes.default.shape({
      onStart: _propTypes.default.func,
      onEnd: _propTypes.default.func,
      onBeginAction: _propTypes.default.func,
      onDropFromOutside: _propTypes.default.func,
      dragFromOutsideItem: _propTypes.default.func,
      draggableAccessor: _propTypes2.accessor,
      resizableAccessor: _propTypes2.accessor,
      dragAndDropAction: _propTypes.default.object,
    }),
  }
  DragAndDropCalendar.propTypes =
    process.env.NODE_ENV !== 'production'
      ? {
          onEventDrop: _propTypes.default.func,
          onEventResize: _propTypes.default.func,
          onDragStart: _propTypes.default.func,
          onDragOver: _propTypes.default.func,
          onDropFromOutside: _propTypes.default.func,
          dragFromOutsideItem: _propTypes.default.func,
          draggableAccessor: _propTypes2.accessor,
          resizableAccessor: _propTypes2.accessor,
          selectable: _propTypes.default.oneOf([true, false, 'ignoreEvents']),
          resizable: _propTypes.default.bool,
          components: _propTypes.default.object,
          elementProps: _propTypes.default.object,
          step: _propTypes.default.number,
        }
      : {}
  return DragAndDropCalendar
}

module.exports = exports['default']
