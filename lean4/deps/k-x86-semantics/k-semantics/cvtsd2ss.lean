def cvtsd2ss1 : instruction :=
  definst "cvtsd2ss" $ do
    pattern fun (v_2556 : reg (bv 128)) (v_2557 : reg (bv 128)) => do
      v_4205 <- getRegister v_2557;
      v_4207 <- getRegister v_2556;
      v_4208 <- eval (extract v_4207 64 128);
      setRegister (lhs.of_reg v_2557) (concat (extract v_4205 0 96) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4208 0 1)) (uvalueMInt (extract v_4208 1 12)) (uvalueMInt (extract v_4208 12 64))) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2550 : Mem) (v_2552 : reg (bv 128)) => do
      v_8432 <- getRegister v_2552;
      v_8434 <- evaluateAddress v_2550;
      v_8435 <- load v_8434 8;
      setRegister (lhs.of_reg v_2552) (concat (extract v_8432 0 96) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8435 0 1)) (uvalueMInt (extract v_8435 1 12)) (uvalueMInt (extract v_8435 12 64))) 24 8) 32));
      pure ()
    pat_end
