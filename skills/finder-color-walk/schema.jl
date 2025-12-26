# FileColorWalk schema (Catlab / ACSets.jl style)
using Catlab
using Catlab.CategoricalAlgebra
using Catlab.CategoricalAlgebra.CSets

@present SchFileColorWalk(FreeSchema) begin
  # objects
  File::Ob
  Fiber::Ob
  Walk::Ob
  Step::Ob
  ColorTrit::Ob
  
  # morphisms
  file_fiber::Hom(File,Fiber)
  step_file::Hom(Step,File)
  step_walk::Hom(Step,Walk)
  
  # attributes
  path::Attr(File,String)
  idx::Attr(Step,Int)
  trit::Attr(ColorTrit,Int)         # 0,1,2
  file_color::Attr(File,Int)        # derived label trit (0..2)
  
  # optional: record policy/seed for reproducibility
  policy::Attr(Walk,String)
  seed::Attr(Walk,String)
end

@acset_type FileColorWalk(SchFileColorWalk, index=[:file_fiber, :step_file, :step_walk])
