/**
 * @name Cross-site scripting
 * @description Writing user input directly to a web page
 *              allows for a cross-site scripting vulnerability.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.1
 * @precision high
 * @id java/customized-xss
 * @tags security
 *       external/cwe/cwe-079
 */

import java
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.security.XSS
import DataFlow::PathGraph

class XSSConfig extends TaintTracking::Configuration {
  XSSConfig() { this = "XSSConfig" }

  override predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }
  
  predicate isWebgoatSink(DataFlow::Node sink) {
    sink.asExpr()
    .(Argument)
    .getCall()
    .getCallee()
    .hasQualifiedName("org.owasp.webgoat.assignments", "AttackResult$AttackResultBuilder",
    ["output", "outputArgs", "feedback", "feedbackArgs"]) 
  }
  
class ReverseTaintStep extends XssAdditionalTaintStep {
  override predicate step(DataFlow::Node node1, DataFlow::Node node2) {
    exists(Method m, MethodAccess ma |
      m.hasQualifiedName("java.lang", "AbstractStringBuilder", "reverse") and
      ma.getMethod().getAnOverride*() = m and
      node1.asExpr() = ma.getQualifier() and
      node2.asExpr() = ma
    )
  }
}

  override predicate isSink(DataFlow::Node sink) {
    (
      sink instanceof XssSink or
      isWebgoatSink(sink)
    )
  }

  override predicate isSanitizer(DataFlow::Node node) { node instanceof XssSanitizer }

  override predicate isSanitizerOut(DataFlow::Node node) { node instanceof XssSinkBarrier }

  override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
    any(XssAdditionalTaintStep s).step(node1, node2)
  }
}

from DataFlow::PathNode source, DataFlow::PathNode sink, XSSConfig conf
where conf.hasFlowPath(source, sink)
select sink.getNode(), source, sink, "Cross-site scripting vulnerability due to $@.",
  source.getNode(), "user-provided value"
