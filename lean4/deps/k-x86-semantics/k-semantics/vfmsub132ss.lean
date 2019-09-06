def vfmsub132ss1 : instruction :=
  definst "vfmsub132ss" $ do
    pattern fun (v_2892 : reg (bv 128)) (v_2893 : reg (bv 128)) (v_2894 : reg (bv 128)) => do
      v_5720 <- getRegister v_2894;
      v_5724 <- getRegister v_2892;
      v_5728 <- getRegister v_2893;
      setRegister (lhs.of_reg v_2894) (concat (extract v_5720 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5720 96 128) 24 8) (MInt2Float (extract v_5724 96 128) 24 8)) (MInt2Float (extract v_5728 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2889 : Mem) (v_2887 : reg (bv 128)) (v_2888 : reg (bv 128)) => do
      v_11607 <- getRegister v_2888;
      v_11611 <- evaluateAddress v_2889;
      v_11612 <- load v_11611 4;
      v_11615 <- getRegister v_2887;
      setRegister (lhs.of_reg v_2888) (concat (extract v_11607 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11607 96 128) 24 8) (MInt2Float v_11612 24 8)) (MInt2Float (extract v_11615 96 128) 24 8)) 32));
      pure ()
    pat_end
