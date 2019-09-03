def dpps1 : instruction :=
  definst "dpps" $ do
    pattern fun (v_2798 : imm int) (v_2801 : reg (bv 128)) (v_2802 : reg (bv 128)) => do
      v_4832 <- eval (handleImmediateWithSignExtend v_2798 8 8);
      v_4837 <- getRegister v_2802;
      v_4838 <- eval (extract v_4837 96 128);
      v_4846 <- getRegister v_2801;
      v_4847 <- eval (extract v_4846 96 128);
      v_4861 <- eval (extract v_4837 64 96);
      v_4869 <- eval (extract v_4846 64 96);
      v_4886 <- eval (extract v_4837 32 64);
      v_4894 <- eval (extract v_4846 32 64);
      v_4908 <- eval (extract v_4837 0 32);
      v_4916 <- eval (extract v_4846 0 32);
      v_4932 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_4832 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4838 0 1)) (uvalueMInt (extract v_4838 1 9)) (uvalueMInt (extract v_4838 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4847 0 1)) (uvalueMInt (extract v_4847 1 9)) (uvalueMInt (extract v_4847 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_4832 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4861 0 1)) (uvalueMInt (extract v_4861 1 9)) (uvalueMInt (extract v_4861 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4869 0 1)) (uvalueMInt (extract v_4869 1 9)) (uvalueMInt (extract v_4869 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_4832 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4886 0 1)) (uvalueMInt (extract v_4886 1 9)) (uvalueMInt (extract v_4886 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4894 0 1)) (uvalueMInt (extract v_4894 1 9)) (uvalueMInt (extract v_4894 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_4832 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4908 0 1)) (uvalueMInt (extract v_4908 1 9)) (uvalueMInt (extract v_4908 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_4916 0 1)) (uvalueMInt (extract v_4916 1 9)) (uvalueMInt (extract v_4916 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2802) (concat (concat (concat (mux (eq (extract v_4832 4 5) (expression.bv_nat 1 1)) v_4932 (expression.bv_nat 32 0)) (mux (eq (extract v_4832 5 6) (expression.bv_nat 1 1)) v_4932 (expression.bv_nat 32 0))) (mux (eq (extract v_4832 6 7) (expression.bv_nat 1 1)) v_4932 (expression.bv_nat 32 0))) (mux (eq (extract v_4832 7 8) (expression.bv_nat 1 1)) v_4932 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2793 : imm int) (v_2794 : Mem) (v_2796 : reg (bv 128)) => do
      v_8842 <- eval (handleImmediateWithSignExtend v_2793 8 8);
      v_8847 <- getRegister v_2796;
      v_8848 <- eval (extract v_8847 96 128);
      v_8856 <- evaluateAddress v_2794;
      v_8857 <- load v_8856 16;
      v_8858 <- eval (extract v_8857 96 128);
      v_8872 <- eval (extract v_8847 64 96);
      v_8880 <- eval (extract v_8857 64 96);
      v_8897 <- eval (extract v_8847 32 64);
      v_8905 <- eval (extract v_8857 32 64);
      v_8919 <- eval (extract v_8847 0 32);
      v_8927 <- eval (extract v_8857 0 32);
      v_8943 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_8842 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8848 0 1)) (uvalueMInt (extract v_8848 1 9)) (uvalueMInt (extract v_8848 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8858 0 1)) (uvalueMInt (extract v_8858 1 9)) (uvalueMInt (extract v_8858 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_8842 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8872 0 1)) (uvalueMInt (extract v_8872 1 9)) (uvalueMInt (extract v_8872 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8880 0 1)) (uvalueMInt (extract v_8880 1 9)) (uvalueMInt (extract v_8880 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_8842 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8897 0 1)) (uvalueMInt (extract v_8897 1 9)) (uvalueMInt (extract v_8897 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8905 0 1)) (uvalueMInt (extract v_8905 1 9)) (uvalueMInt (extract v_8905 9 32)))) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_8842 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8919 0 1)) (uvalueMInt (extract v_8919 1 9)) (uvalueMInt (extract v_8919 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_8927 0 1)) (uvalueMInt (extract v_8927 1 9)) (uvalueMInt (extract v_8927 9 32)))) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_2796) (concat (concat (concat (mux (eq (extract v_8842 4 5) (expression.bv_nat 1 1)) v_8943 (expression.bv_nat 32 0)) (mux (eq (extract v_8842 5 6) (expression.bv_nat 1 1)) v_8943 (expression.bv_nat 32 0))) (mux (eq (extract v_8842 6 7) (expression.bv_nat 1 1)) v_8943 (expression.bv_nat 32 0))) (mux (eq (extract v_8842 7 8) (expression.bv_nat 1 1)) v_8943 (expression.bv_nat 32 0)));
      pure ()
    pat_end
