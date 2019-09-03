def vmulss1 : instruction :=
  definst "vmulss" $ do
    pattern fun (v_3137 : reg (bv 128)) (v_3138 : reg (bv 128)) (v_3139 : reg (bv 128)) => do
      v_5867 <- getRegister v_3138;
      v_5869 <- eval (extract v_5867 96 128);
      v_5877 <- getRegister v_3137;
      v_5878 <- eval (extract v_5877 96 128);
      setRegister (lhs.of_reg v_3139) (concat (extract v_5867 0 96) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5869 0 1)) (uvalueMInt (extract v_5869 1 9)) (uvalueMInt (extract v_5869 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5878 0 1)) (uvalueMInt (extract v_5878 1 9)) (uvalueMInt (extract v_5878 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_3132 : Mem) (v_3133 : reg (bv 128)) (v_3134 : reg (bv 128)) => do
      v_11602 <- getRegister v_3133;
      v_11604 <- eval (extract v_11602 96 128);
      v_11612 <- evaluateAddress v_3132;
      v_11613 <- load v_11612 4;
      setRegister (lhs.of_reg v_3134) (concat (extract v_11602 0 96) (Float2MInt (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11604 0 1)) (uvalueMInt (extract v_11604 1 9)) (uvalueMInt (extract v_11604 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_11613 0 1)) (uvalueMInt (extract v_11613 1 9)) (uvalueMInt (extract v_11613 9 32)))) 32));
      pure ()
    pat_end
