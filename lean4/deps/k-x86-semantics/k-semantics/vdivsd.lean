def vdivsd1 : instruction :=
  definst "vdivsd" $ do
    pattern fun (v_3482 : reg (bv 128)) (v_3483 : reg (bv 128)) (v_3484 : reg (bv 128)) => do
      v_6530 <- getRegister v_3483;
      v_6534 <- getRegister v_3482;
      setRegister (lhs.of_reg v_3484) (concat (extract v_6530 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6530 64 128) 53 11) (MInt2Float (extract v_6534 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3474 : Mem) (v_3477 : reg (bv 128)) (v_3478 : reg (bv 128)) => do
      v_10526 <- getRegister v_3477;
      v_10530 <- evaluateAddress v_3474;
      v_10531 <- load v_10530 8;
      setRegister (lhs.of_reg v_3478) (concat (extract v_10526 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10526 64 128) 53 11) (MInt2Float v_10531 53 11)) 64));
      pure ()
    pat_end
