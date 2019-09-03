def vsubsd1 : instruction :=
  definst "vsubsd" $ do
    pattern fun (v_2405 : reg (bv 128)) (v_2406 : reg (bv 128)) (v_2407 : reg (bv 128)) => do
      v_3357 <- getRegister v_2406;
      v_3361 <- getRegister v_2405;
      setRegister (lhs.of_reg v_2407) (concat (extract v_3357 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3357 64 128) 53 11) (MInt2Float (extract v_3361 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2400 : Mem) (v_2401 : reg (bv 128)) (v_2402 : reg (bv 128)) => do
      v_6638 <- getRegister v_2401;
      v_6642 <- evaluateAddress v_2400;
      v_6643 <- load v_6642 8;
      setRegister (lhs.of_reg v_2402) (concat (extract v_6638 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6638 64 128) 53 11) (MInt2Float v_6643 53 11)) 64));
      pure ()
    pat_end
