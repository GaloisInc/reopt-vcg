def vdivss1 : instruction :=
  definst "vdivss" $ do
    pattern fun (v_3466 : reg (bv 128)) (v_3467 : reg (bv 128)) (v_3468 : reg (bv 128)) => do
      v_6519 <- getRegister v_3467;
      v_6523 <- getRegister v_3466;
      setRegister (lhs.of_reg v_3468) (concat (extract v_6519 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6519 96 128) 24 8) (MInt2Float (extract v_6523 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3460 : Mem) (v_3461 : reg (bv 128)) (v_3462 : reg (bv 128)) => do
      v_10510 <- getRegister v_3461;
      v_10514 <- evaluateAddress v_3460;
      v_10515 <- load v_10514 4;
      setRegister (lhs.of_reg v_3462) (concat (extract v_10510 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10510 96 128) 24 8) (MInt2Float v_10515 24 8)) 32));
      pure ()
    pat_end
