def vfnmadd231ss1 : instruction :=
  definst "vfnmadd231ss" $ do
    pattern fun (v_3265 : reg (bv 128)) (v_3266 : reg (bv 128)) (v_3267 : reg (bv 128)) => do
      v_7215 <- getRegister v_3267;
      v_7217 <- getRegister v_3266;
      v_7220 <- getRegister v_3265;
      v_7226 <- eval (MInt2Float (extract v_7215 96 128) 24 8);
      setRegister (lhs.of_reg v_3267) (concat (extract v_7215 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7217 96 128) 24 8) (MInt2Float (extract v_7220 96 128) 24 8))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_7226)) v_7226) 32) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3262 : Mem) (v_3260 : reg (bv 128)) (v_3261 : reg (bv 128)) => do
      v_12907 <- getRegister v_3261;
      v_12909 <- getRegister v_3260;
      v_12912 <- evaluateAddress v_3262;
      v_12913 <- load v_12912 4;
      v_12918 <- eval (MInt2Float (extract v_12907 96 128) 24 8);
      setRegister (lhs.of_reg v_3261) (concat (extract v_12907 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_12909 96 128) 24 8) (MInt2Float v_12913 24 8))) (MInt2Float (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT 0e+00 v_12918)) v_12918) 32) 24 8)) 32));
      pure ()
    pat_end
