def vfnmsub213ss1 : instruction :=
  definst "vfnmsub213ss" $ do
    pattern fun (v_3462 : reg (bv 128)) (v_3463 : reg (bv 128)) (v_3464 : reg (bv 128)) => do
      v_7841 <- getRegister v_3464;
      v_7843 <- getRegister v_3463;
      v_7850 <- getRegister v_3462;
      setRegister (lhs.of_reg v_3464) (concat (extract v_7841 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7843 96 128) 24 8) (MInt2Float (extract v_7841 96 128) 24 8))) (MInt2Float (extract v_7850 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3456 : Mem) (v_3457 : reg (bv 128)) (v_3458 : reg (bv 128)) => do
      v_13498 <- getRegister v_3458;
      v_13500 <- getRegister v_3457;
      v_13507 <- evaluateAddress v_3456;
      v_13508 <- load v_13507 4;
      setRegister (lhs.of_reg v_3458) (concat (extract v_13498 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13500 96 128) 24 8) (MInt2Float (extract v_13498 96 128) 24 8))) (MInt2Float v_13508 24 8)) 32));
      pure ()
    pat_end
