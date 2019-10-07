//------------------------------------------------------------------------------
// Tooling sample. Demonstrates:
//
// * How to write a simple source tool using libTooling.
// * How to use RecursiveASTVisitor to find interesting AST nodes.
// * How to use the Rewriter API to rewrite the source code.
//
// Eli Bendersky (eliben@gmail.com)
// This code is in the public domain
//------------------------------------------------------------------------------
#include <sstream>
#include <string>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;

static llvm::cl::OptionCategory ToolingSampleCategory("Tooling Sample");

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
  MyASTVisitor(Rewriter &R) : TheRewriter(R) {}


  void   printPropertyExpressionReceiver( ObjCPropertyRefExpr *Expr,
                                          std::stringstream &Stream)
  {
    if( Expr->isSuperReceiver())
       Stream << "super";
    else
      if( Expr->isObjectReceiver() && Expr->getBase())
      {
         SourceManager   *SM;
         const char      *startBuf;
         const char      *endBuf;

         SM = &TheRewriter.getSourceMgr();

         endBuf = SM->getCharacterData( Expr->getLocation());
         if( Expr->getReceiverLocation().isValid())
         {
            startBuf = SM->getCharacterData( Expr->getReceiverLocation());
         }
         else
         {
            startBuf = SM->getCharacterData( Expr->getBase()->getBeginLoc());
         }

         while( endBuf > startBuf)
         {
            switch( endBuf[ -1])
            {
               case ' '  :
               case '\t' :
               case '.'  :
                  --endBuf;
                  continue;
             }
             break;
         }

         if( endBuf == startBuf)
            Stream << "self";
         else
         {
            std::string  receiver( startBuf, (endBuf - startBuf));
            Stream << receiver;
         }
      }
      else
         if( Expr->isClassReceiver() && Expr->getClassReceiver())
            Stream << Expr->getClassReceiver()->getName().str();
         else
            Stream << "self";
  }

  void   printPropertyExpressionSelector( ObjCPropertyRefExpr *Expr,
                                          std::stringstream &Stream)
  {
    Selector   Sel;

    if( Expr->isMessagingGetter())
    {
       Sel = Expr->getGetterSelector();
       Stream << Sel.getAsString() << "]";
    }
    else
    {
       Sel = Expr->getSetterSelector();
       Stream << Sel.getAsString(); // closer done by BinaryOp
       // Stream << value;
    }
  }


/*
  bool VisitBinaryOperator(BinaryOperator  *Stmt) {
     if( Stmt->getOpcode() == BO_Assign && isa<ObjCPropertyRefExpr>( Stmt->getLHS()))
     {
        std::stringstream  Stream;
        const char         *startBuf;
        const char         *endBuf;
        SourceManager      *SM;

        SM = &TheRewriter.getSourceMgr();

        // fprintf( stderr, "clear\n");

        // remove setter assignment text
        startBuf = SM->getCharacterData( Stmt->getEndLoc());
        endBuf   = startBuf;
        endBuf  += Lexer::MeasureTokenLength( Stmt->getEndLoc(), *SM, TheRewriter.getLangOpts());


        std::string  value( startBuf, (endBuf - startBuf));

        fprintf( stderr, "2write: \"%s\"\n", value.c_str());
        printPropertyExpression( (ObjCPropertyRefExpr *) Stmt->getLHS(), Stream, value);
        TheRewriter.ReplaceText( SourceRange( Stmt->getBeginLoc(), Stmt->getEndLoc()), Stream.str());
     }
     return( true);
  }
*/


  bool VisitObjCPropertyRefExpr( ObjCPropertyRefExpr *Expr) {
    SourceManager   *SM;
    int             startLength;
    int             prefixLength;
    int             endLength;
    int             dotLength;
    const char      *startBuf;
    const char      *endBuf;
    const char      *prefixEndBuf;
    const char      *dotBuf;
    const char      *s;

    SM           = &TheRewriter.getSourceMgr();
    startBuf     = SM->getCharacterData( Expr->getBeginLoc());
    endBuf       = SM->getCharacterData( Expr->getEndLoc());
    startLength  = Lexer::MeasureTokenLength( Expr->getBeginLoc(), *SM, TheRewriter.getLangOpts());
    endLength    = Lexer::MeasureTokenLength( Expr->getEndLoc(), *SM, TheRewriter.getLangOpts());
    prefixLength = endBuf - startBuf;

    std::string  value( startBuf, (endBuf - startBuf) + endLength);
    fprintf( stderr, "rewrite: \"%s\" (S=\"%.*s\" P=\"%.*s\" E=\"%.*s\")\n", value.c_str(),
                        startLength, startBuf,
                        prefixLength, startBuf,
                        endLength, endBuf);

   // rewrite: "a . x" (S="a" P="a . " E="x")
   // rewrite: "b.foo.x" (S="b" P="b.foo." E="x")
   // rewrite: "b.foo" (S="b" P="b." E="foo")
   // rewrite: "c.foo.foo.x" (S="c" P="c.foo.foo." E="x")
   // rewrite: "c.foo.foo" (S="c" P="c.foo." E="foo")
   // rewrite: "c.foo" (S="c" P="c." E="foo")

    // find dots and eradicated leading and trailing spaces
    prefixEndBuf = &startBuf[ prefixLength];
    s      = prefixEndBuf;
    dotBuf = NULL;
    while( --s > startBuf)
    {
      switch( *s)
      {
         case '\t' : case '\r' : case '\n' : case ' ' :
            if( dotBuf)
               dotBuf = s;
            continue;

         case '.' :
            dotBuf = s;
            continue;
      }
      break;
    }

    // this can't really happen
    if( ! dotBuf)
      return false;

    dotLength = prefixEndBuf - dotBuf;

    // remove the dot now
    TheRewriter.RemoveText( Expr->getBeginLoc().getLocWithOffset( prefixLength - dotLength), dotLength);


    std::stringstream  Receiver;
    Receiver << "[";
    printPropertyExpressionReceiver( Expr, Receiver);

    std::stringstream  Selector;
    Selector << " ";
    printPropertyExpressionSelector( Expr, Selector);

    //     ... = this is endLength
    // foo.xxx
    // ^   ^
    // |    \----Expr->getLocation() same as Expr->getEndLoc()
    // |
    // \-----Expr->getBeginLoc()
    //

    fprintf( stderr, "selector: \"%s\"\n", Selector.str().c_str());
    ;
    TheRewriter.InsertText( Expr->getBeginLoc(), "[");
    TheRewriter.InsertText( Expr->getLocation().getLocWithOffset( endLength), Selector.str());
    TheRewriter.RemoveText( Expr->getEndLoc(), endLength);
//    TheRewriter.InsertText(Expr->getLocation(), "L"); //
//    TheRewriter.InsertText(Expr->getEndLoc(), "E");
//    TheRewriter.InsertText(Expr->getSourceRange().getBegin(), "[");
//    TheRewriter.InsertText(Expr->getSourceRange().getEnd(), "]");
//    TheRewriter.InsertText(Expr->getSourceRange().getEnd().getLocWithOffset(-1), ">");
//    TheRewriter.InsertText(Expr->getOperatorLoc(), " ]");
    return true;
  }


  bool VisitBinaryOperator( BinaryOperator *Stmt) {
    SourceManager         *SM;
    int                   length;
    const char            *opBuf;
    const char            *endBuf;
    const char            *closerBuf;
    const char            *exprEndBuf;
    const char            *startBuf;
    const char            *s;
    static int            i;
    int                   frontLength;  // from start
    int                   opLength;
    int                   endLength;
    int                   exprEndLength;
    int                   endBufLength;
    int                   opOffset;
    ObjCPropertyRefExpr   *Expr;

    if( Stmt->getOpcode() != BO_Assign || ! isa<ObjCPropertyRefExpr>( Stmt->getLHS()))
      return( true);

    Expr = dyn_cast<ObjCPropertyRefExpr>( Stmt->getLHS());

    SM            = &TheRewriter.getSourceMgr();
    exprEndBuf    = SM->getCharacterData( Expr->getEndLoc());
    exprEndLength = Lexer::MeasureTokenLength( Expr->getEndLoc(), *SM, TheRewriter.getLangOpts());
    closerBuf     = &exprEndBuf[ exprEndLength - 1];

    fprintf( stderr, "expr: (E=\"%.*s\" C=\"%.*s\")\n",
                        exprEndLength, exprEndBuf,
                        1, closerBuf);

    startBuf     = SM->getCharacterData( Stmt->getBeginLoc());
    opBuf        = SM->getCharacterData( Stmt->getOperatorLoc());
    endBuf       = SM->getCharacterData( Stmt->getEndLoc());
    endBufLength = Lexer::MeasureTokenLength( Stmt->getEndLoc(), *SM, TheRewriter.getLangOpts());

    s        = opBuf;
    opOffset = 0;
    while( --s >= startBuf)
    {
      switch( *s)
      {
         case '\t' : case '\r' : case '\n' : case ' ' :
            opOffset++;
            continue;
      }
      break;
    }

    TheRewriter.RemoveText( Stmt->getOperatorLoc().getLocWithOffset( -opOffset), endBuf - opBuf + opOffset);
    TheRewriter.InsertText( Stmt->getEndLoc().getLocWithOffset( endBufLength), "]");

    // fprintf( stderr, "rewrite: \"%s\" -> \"%s\"\n", origin.c_str(), replace.c_str());
    // TheRewriter.ReplaceText( Stmt->getBeginLoc(), length, replace);

    return true;
  }



/*
  bool VisitObjCPropertyRefExpr(ObjCPropertyRefExpr *Expr) {
    std::stringstream  Stream;
    std::string        value( "unused");
    int                n;
    SourceManager      *SM;
    int                length;
    const char         *startBuf;
    const char         *endBuf;

    printPropertyExpression( Expr, Stream, value);

    SM       = &TheRewriter.getSourceMgr();
    endBuf   = SM->getCharacterData( Expr->getEndLoc());
    startBuf = SM->getCharacterData( Expr->getBeginLoc());
    length   = endBuf - startBuf;
    length  += Lexer::MeasureTokenLength( Expr->getEndLoc(), *SM, TheRewriter.getLangOpts());

    std::string  tmp( startBuf, length);

    fprintf( stderr, "rewrite: \"%s\" -> \"%s\"\n", tmp.c_str(), Stream.str().c_str());
    TheRewriter.ReplaceText( Expr->getBeginLoc(), length, Stream.str());

    return true;
  }
*/

private:
  Rewriter &TheRewriter;
};


// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
  MyASTConsumer(Rewriter &R) : Visitor(R) {}

  // Override the method that gets called for each parsed top-level
  // declaration.
  bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
      // Traverse the declaration using our AST visitor.
      Visitor.TraverseDecl(*b);
      // (*b)->dump();
    }
    return true;
  }

private:
  MyASTVisitor Visitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
public:
  MyFrontendAction() {}
  void EndSourceFileAction() override {
    SourceManager &SM = TheRewriter.getSourceMgr();
    llvm::errs() << "** EndSourceFileAction for: "
                 << SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";

    // Now emit the rewritten buffer.
    TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
  }

  std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {
    llvm::errs() << "** Creating AST consumer for: " << file << "\n";
    TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
    return llvm::make_unique<MyASTConsumer>(TheRewriter);
  }

private:
  Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
  CommonOptionsParser op(argc, argv, ToolingSampleCategory);
  ClangTool Tool(op.getCompilations(), op.getSourcePathList());

  // ClangTool::run accepts a FrontendActionFactory, which is then used to
  // create new objects implementing the FrontendAction interface. Here we use
  // the helper newFrontendActionFactory to create a default factory that will
  // return a new MyFrontendAction object every time.
  // To further customize this, we could create our own factory class.
  return Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
}
