def vdivss1 : instruction :=
  definst "vdivss" $ do
    pattern fun (v_3493 : reg (bv 128)) (v_3494 : reg (bv 128)) (v_3495 : reg (bv 128)) => do
      v_6546 <- getRegister v_3494;
      v_6550 <- getRegister v_3493;
      setRegister (lhs.of_reg v_3495) (concat (extract v_6546 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6546 96 128) 24 8) (MInt2Float (extract v_6550 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3485 : Mem) (v_3488 : reg (bv 128)) (v_3489 : reg (bv 128)) => do
      v_10537 <- getRegister v_3488;
      v_10541 <- evaluateAddress v_3485;
      v_10542 <- load v_10541 4;
      setRegister (lhs.of_reg v_3489) (concat (extract v_10537 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10537 96 128) 24 8) (MInt2Float v_10542 24 8)) 32));
      pure ()
    pat_end
