def vfmadd231sd1 : instruction :=
  definst "vfmadd231sd" $ do
    pattern fun (v_2683 : reg (bv 128)) (v_2684 : reg (bv 128)) (v_2685 : reg (bv 128)) => do
      v_4824 <- getRegister v_2685;
      v_4826 <- getRegister v_2684;
      v_4829 <- getRegister v_2683;
      setRegister (lhs.of_reg v_2685) (concat (extract v_4824 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4826 64 128) 53 11) (MInt2Float (extract v_4829 64 128) 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_4824 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2680 : Mem) (v_2678 : reg (bv 128)) (v_2679 : reg (bv 128)) => do
      v_10790 <- getRegister v_2679;
      v_10792 <- getRegister v_2678;
      v_10795 <- evaluateAddress v_2680;
      v_10796 <- load v_10795 8;
      setRegister (lhs.of_reg v_2679) (concat (extract v_10790 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10792 64 128) 53 11) (MInt2Float v_10796 53 11)) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) (MInt2Float (extract v_10790 64 128) 53 11)) 64) 53 11)) 64));
      pure ()
    pat_end
