def vfmsub132sd1 : instruction :=
  definst "vfmsub132sd" $ do
    pattern fun (v_2881 : reg (bv 128)) (v_2882 : reg (bv 128)) (v_2883 : reg (bv 128)) => do
      v_5700 <- getRegister v_2883;
      v_5704 <- getRegister v_2881;
      v_5708 <- getRegister v_2882;
      setRegister (lhs.of_reg v_2883) (concat (extract v_5700 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5700 64 128) 53 11) (MInt2Float (extract v_5704 64 128) 53 11)) (MInt2Float (extract v_5708 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2878 : Mem) (v_2876 : reg (bv 128)) (v_2877 : reg (bv 128)) => do
      v_11592 <- getRegister v_2877;
      v_11596 <- evaluateAddress v_2878;
      v_11597 <- load v_11596 8;
      v_11600 <- getRegister v_2876;
      setRegister (lhs.of_reg v_2877) (concat (extract v_11592 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11592 64 128) 53 11) (MInt2Float v_11597 53 11)) (MInt2Float (extract v_11600 64 128) 53 11)) 64));
      pure ()
    pat_end
