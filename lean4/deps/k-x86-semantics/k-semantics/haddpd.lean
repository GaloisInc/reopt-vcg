def haddpd1 : instruction :=
  definst "haddpd" $ do
    pattern fun (v_2827 : reg (bv 128)) (v_2828 : reg (bv 128)) => do
      v_4977 <- getRegister v_2827;
      v_4978 <- eval (extract v_4977 64 128);
      v_4986 <- eval (extract v_4977 0 64);
      v_4996 <- getRegister v_2828;
      v_4997 <- eval (extract v_4996 64 128);
      v_5005 <- eval (extract v_4996 0 64);
      setRegister (lhs.of_reg v_2828) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4978 0 1)) (uvalueMInt (extract v_4978 1 12)) (uvalueMInt (extract v_4978 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4986 0 1)) (uvalueMInt (extract v_4986 1 12)) (uvalueMInt (extract v_4986 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_4997 0 1)) (uvalueMInt (extract v_4997 1 12)) (uvalueMInt (extract v_4997 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_5005 0 1)) (uvalueMInt (extract v_5005 1 12)) (uvalueMInt (extract v_5005 12 64)))) 64));
      pure ()
    pat_end;
    pattern fun (v_2821 : Mem) (v_2823 : reg (bv 128)) => do
      v_8959 <- evaluateAddress v_2821;
      v_8960 <- load v_8959 16;
      v_8961 <- eval (extract v_8960 64 128);
      v_8969 <- eval (extract v_8960 0 64);
      v_8979 <- getRegister v_2823;
      v_8980 <- eval (extract v_8979 64 128);
      v_8988 <- eval (extract v_8979 0 64);
      setRegister (lhs.of_reg v_2823) (concat (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8961 0 1)) (uvalueMInt (extract v_8961 1 12)) (uvalueMInt (extract v_8961 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8969 0 1)) (uvalueMInt (extract v_8969 1 12)) (uvalueMInt (extract v_8969 12 64)))) 64) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8980 0 1)) (uvalueMInt (extract v_8980 1 12)) (uvalueMInt (extract v_8980 12 64))) (MIntToFloatImpl 53 11 (uvalueMInt (extract v_8988 0 1)) (uvalueMInt (extract v_8988 1 12)) (uvalueMInt (extract v_8988 12 64)))) 64));
      pure ()
    pat_end
