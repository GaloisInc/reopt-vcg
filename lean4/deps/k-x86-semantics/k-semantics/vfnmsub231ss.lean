def vfnmsub231ss1 : instruction :=
  definst "vfnmsub231ss" $ do
    pattern fun (v_3528 : reg (bv 128)) (v_3529 : reg (bv 128)) (v_3530 : reg (bv 128)) => do
      v_8126 <- getRegister v_3530;
      v_8128 <- getRegister v_3529;
      v_8131 <- getRegister v_3528;
      setRegister (lhs.of_reg v_3530) (concat (extract v_8126 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_8128 96 128) 24 8) (MInt2Float (extract v_8131 96 128) 24 8))) (MInt2Float (extract v_8126 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3522 : Mem) (v_3523 : reg (bv 128)) (v_3524 : reg (bv 128)) => do
      v_13757 <- getRegister v_3524;
      v_13759 <- getRegister v_3523;
      v_13762 <- evaluateAddress v_3522;
      v_13763 <- load v_13762 4;
      setRegister (lhs.of_reg v_3524) (concat (extract v_13757 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13759 96 128) 24 8) (MInt2Float v_13763 24 8))) (MInt2Float (extract v_13757 96 128) 24 8)) 32));
      pure ()
    pat_end
