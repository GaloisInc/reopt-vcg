def vfmsub132ss1 : instruction :=
  definst "vfmsub132ss" $ do
    pattern fun (v_2803 : reg (bv 128)) (v_2804 : reg (bv 128)) (v_2805 : reg (bv 128)) => do
      v_5626 <- getRegister v_2805;
      v_5630 <- getRegister v_2803;
      v_5634 <- getRegister v_2804;
      setRegister (lhs.of_reg v_2805) (concat (extract v_5626 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5626 96 128) 24 8) (MInt2Float (extract v_5630 96 128) 24 8)) (MInt2Float (extract v_5634 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2800 : Mem) (v_2798 : reg (bv 128)) (v_2799 : reg (bv 128)) => do
      v_11496 <- getRegister v_2799;
      v_11500 <- evaluateAddress v_2800;
      v_11501 <- load v_11500 4;
      v_11504 <- getRegister v_2798;
      setRegister (lhs.of_reg v_2799) (concat (extract v_11496 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11496 96 128) 24 8) (MInt2Float v_11501 24 8)) (MInt2Float (extract v_11504 96 128) 24 8)) 32));
      pure ()
    pat_end
