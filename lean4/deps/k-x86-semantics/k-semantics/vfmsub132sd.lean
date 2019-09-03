def vfmsub132sd1 : instruction :=
  definst "vfmsub132sd" $ do
    pattern fun (v_2792 : reg (bv 128)) (v_2793 : reg (bv 128)) (v_2794 : reg (bv 128)) => do
      v_5606 <- getRegister v_2794;
      v_5610 <- getRegister v_2792;
      v_5614 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2794) (concat (extract v_5606 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5606 64 128) 53 11) (MInt2Float (extract v_5610 64 128) 53 11)) (MInt2Float (extract v_5614 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2789 : Mem) (v_2787 : reg (bv 128)) (v_2788 : reg (bv 128)) => do
      v_11481 <- getRegister v_2788;
      v_11485 <- evaluateAddress v_2789;
      v_11486 <- load v_11485 8;
      v_11489 <- getRegister v_2787;
      setRegister (lhs.of_reg v_2788) (concat (extract v_11481 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11481 64 128) 53 11) (MInt2Float v_11486 53 11)) (MInt2Float (extract v_11489 64 128) 53 11)) 64));
      pure ()
    pat_end
