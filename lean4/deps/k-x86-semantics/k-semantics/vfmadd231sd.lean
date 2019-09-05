def vfmadd231sd1 : instruction :=
  definst "vfmadd231sd" $ do
    pattern fun (v_2659 : reg (bv 128)) (v_2660 : reg (bv 128)) (v_2661 : reg (bv 128)) => do
      v_4797 <- getRegister v_2661;
      v_4799 <- getRegister v_2660;
      v_4802 <- getRegister v_2659;
      setRegister (lhs.of_reg v_2661) (concat (extract v_4797 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4799 64 128) 53 11) (MInt2Float (extract v_4802 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4797 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2653 : Mem) (v_2654 : reg (bv 128)) (v_2655 : reg (bv 128)) => do
      v_10763 <- getRegister v_2655;
      v_10765 <- getRegister v_2654;
      v_10768 <- evaluateAddress v_2653;
      v_10769 <- load v_10768 8;
      setRegister (lhs.of_reg v_2655) (concat (extract v_10763 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10765 64 128) 53 11) (MInt2Float v_10769 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10763 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end
