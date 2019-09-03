def dpps1 : instruction :=
  definst "dpps" $ do
    pattern fun (v_2789 : imm int) (v_2787 : reg (bv 128)) (v_2788 : reg (bv 128)) => do
      v_4692 <- eval (handleImmediateWithSignExtend v_2789 8 8);
      v_4697 <- getRegister v_2788;
      v_4700 <- getRegister v_2787;
      v_4744 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_4692 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4697 96 128) 24 8) (MInt2Float (extract v_4700 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_4692 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4697 64 96) 24 8) (MInt2Float (extract v_4700 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_4692 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4697 32 64) 24 8) (MInt2Float (extract v_4700 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_4692 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4697 0 32) 24 8) (MInt2Float (extract v_4700 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2788) (concat (concat (concat (mux (eq (extract v_4692 4 5) (expression.bv_nat 1 1)) v_4744 (expression.bv_nat 32 0)) (mux (eq (extract v_4692 5 6) (expression.bv_nat 1 1)) v_4744 (expression.bv_nat 32 0))) (mux (eq (extract v_4692 6 7) (expression.bv_nat 1 1)) v_4744 (expression.bv_nat 32 0))) (mux (eq (extract v_4692 7 8) (expression.bv_nat 1 1)) v_4744 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2784 : imm int) (v_2782 : Mem) (v_2783 : reg (bv 128)) => do
      v_8414 <- eval (handleImmediateWithSignExtend v_2784 8 8);
      v_8419 <- getRegister v_2783;
      v_8422 <- evaluateAddress v_2782;
      v_8423 <- load v_8422 16;
      v_8467 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_8414 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8419 96 128) 24 8) (MInt2Float (extract v_8423 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_8414 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8419 64 96) 24 8) (MInt2Float (extract v_8423 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_8414 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8419 32 64) 24 8) (MInt2Float (extract v_8423 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_8414 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8419 0 32) 24 8) (MInt2Float (extract v_8423 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2783) (concat (concat (concat (mux (eq (extract v_8414 4 5) (expression.bv_nat 1 1)) v_8467 (expression.bv_nat 32 0)) (mux (eq (extract v_8414 5 6) (expression.bv_nat 1 1)) v_8467 (expression.bv_nat 32 0))) (mux (eq (extract v_8414 6 7) (expression.bv_nat 1 1)) v_8467 (expression.bv_nat 32 0))) (mux (eq (extract v_8414 7 8) (expression.bv_nat 1 1)) v_8467 (expression.bv_nat 32 0)));
      pure ()
    pat_end
