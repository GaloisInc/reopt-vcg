def vfmsub231sd1 : instruction :=
  definst "vfmsub231sd" $ do
    pattern fun (v_3013 : reg (bv 128)) (v_3014 : reg (bv 128)) (v_3015 : reg (bv 128)) => do
      v_6207 <- getRegister v_3015;
      v_6209 <- getRegister v_3014;
      v_6212 <- getRegister v_3013;
      setRegister (lhs.of_reg v_3015) (concat (extract v_6207 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6209 64 128) 53 11) (MInt2Float (extract v_6212 64 128) 53 11)) (MInt2Float (extract v_6207 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3010 : Mem) (v_3008 : reg (bv 128)) (v_3009 : reg (bv 128)) => do
      v_12047 <- getRegister v_3009;
      v_12049 <- getRegister v_3008;
      v_12052 <- evaluateAddress v_3010;
      v_12053 <- load v_12052 8;
      setRegister (lhs.of_reg v_3009) (concat (extract v_12047 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12049 64 128) 53 11) (MInt2Float v_12053 53 11)) (MInt2Float (extract v_12047 64 128) 53 11)) 64));
      pure ()
    pat_end
