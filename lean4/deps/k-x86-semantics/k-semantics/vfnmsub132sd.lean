def vfnmsub132sd1 : instruction :=
  definst "vfnmsub132sd" $ do
    pattern fun (v_3320 : reg (bv 128)) (v_3321 : reg (bv 128)) (v_3322 : reg (bv 128)) => do
      v_7471 <- getRegister v_3322;
      v_7475 <- getRegister v_3320;
      v_7480 <- getRegister v_3321;
      setRegister (lhs.of_reg v_3322) (concat (extract v_7471 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_7471 64 128) 53 11) (MInt2Float (extract v_7475 64 128) 53 11))) (MInt2Float (extract v_7480 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3315 : reg (bv 128)) (v_3316 : reg (bv 128)) => do
      v_13142 <- getRegister v_3316;
      v_13146 <- evaluateAddress v_3317;
      v_13147 <- load v_13146 8;
      v_13151 <- getRegister v_3315;
      setRegister (lhs.of_reg v_3316) (concat (extract v_13142 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT -1e+00 (_*Float__FLOAT (MInt2Float (extract v_13142 64 128) 53 11) (MInt2Float v_13147 53 11))) (MInt2Float (extract v_13151 64 128) 53 11)) 64));
      pure ()
    pat_end
