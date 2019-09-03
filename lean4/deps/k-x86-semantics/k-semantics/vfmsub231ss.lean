def vfmsub231ss1 : instruction :=
  definst "vfmsub231ss" $ do
    pattern fun (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) (v_2937 : reg (bv 128)) => do
      v_6133 <- getRegister v_2937;
      v_6135 <- getRegister v_2936;
      v_6138 <- getRegister v_2935;
      setRegister (lhs.of_reg v_2937) (concat (extract v_6133 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6135 96 128) 24 8) (MInt2Float (extract v_6138 96 128) 24 8)) (MInt2Float (extract v_6133 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2932 : Mem) (v_2930 : reg (bv 128)) (v_2931 : reg (bv 128)) => do
      v_11951 <- getRegister v_2931;
      v_11953 <- getRegister v_2930;
      v_11956 <- evaluateAddress v_2932;
      v_11957 <- load v_11956 4;
      setRegister (lhs.of_reg v_2931) (concat (extract v_11951 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11953 96 128) 24 8) (MInt2Float v_11957 24 8)) (MInt2Float (extract v_11951 96 128) 24 8)) 32));
      pure ()
    pat_end
