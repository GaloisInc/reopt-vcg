def addss1 : instruction :=
  definst "addss" $ do
    pattern fun (v_2663 : reg (bv 128)) (v_2664 : reg (bv 128)) => do
      v_5026 <- getRegister v_2664;
      v_5028 <- eval (extract v_5026 96 128);
      v_5036 <- getRegister v_2663;
      v_5037 <- eval (extract v_5036 96 128);
      setRegister (lhs.of_reg v_2664) (concat (extract v_5026 0 96) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5028 0 1)) (uvalueMInt (extract v_5028 1 9)) (uvalueMInt (extract v_5028 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5037 0 1)) (uvalueMInt (extract v_5037 1 9)) (uvalueMInt (extract v_5037 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2658 : Mem) (v_2659 : reg (bv 128)) => do
      v_9419 <- getRegister v_2659;
      v_9421 <- eval (extract v_9419 96 128);
      v_9429 <- evaluateAddress v_2658;
      v_9430 <- load v_9429 4;
      setRegister (lhs.of_reg v_2659) (concat (extract v_9419 0 96) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9421 0 1)) (uvalueMInt (extract v_9421 1 9)) (uvalueMInt (extract v_9421 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_9430 0 1)) (uvalueMInt (extract v_9430 1 9)) (uvalueMInt (extract v_9430 9 32)))) 32));
      pure ()
    pat_end
