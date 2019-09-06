def vfnmsub213ss1 : instruction :=
  definst "vfnmsub213ss" $ do
    pattern fun (v_3486 : reg (bv 128)) (v_3487 : reg (bv 128)) (v_3488 : reg (bv 128)) => do
      v_7868 <- getRegister v_3488;
      v_7870 <- getRegister v_3487;
      v_7877 <- getRegister v_3486;
      setRegister (lhs.of_reg v_3488) (concat (extract v_7868 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7870 96 128) 24 8) (MInt2Float (extract v_7868 96 128) 24 8))) (MInt2Float (extract v_7877 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3483 : Mem) (v_3481 : reg (bv 128)) (v_3482 : reg (bv 128)) => do
      v_13525 <- getRegister v_3482;
      v_13527 <- getRegister v_3481;
      v_13534 <- evaluateAddress v_3483;
      v_13535 <- load v_13534 4;
      setRegister (lhs.of_reg v_3482) (concat (extract v_13525 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13527 96 128) 24 8) (MInt2Float (extract v_13525 96 128) 24 8))) (MInt2Float v_13535 24 8)) 32));
      pure ()
    pat_end
