def subpd1 : instruction :=
  definst "subpd" $ do
    pattern fun (v_3270 : reg (bv 128)) (v_3271 : reg (bv 128)) => do
      v_5889 <- getRegister v_3271;
      v_5892 <- getRegister v_3270;
      setRegister (lhs.of_reg v_3271) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5889 0 64) 53 11) (MInt2Float (extract v_5892 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_5889 64 128) 53 11) (MInt2Float (extract v_5892 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3266 : Mem) (v_3267 : reg (bv 128)) => do
      v_8678 <- getRegister v_3267;
      v_8681 <- evaluateAddress v_3266;
      v_8682 <- load v_8681 16;
      setRegister (lhs.of_reg v_3267) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8678 0 64) 53 11) (MInt2Float (extract v_8682 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8678 64 128) 53 11) (MInt2Float (extract v_8682 64 128) 53 11)) 64));
      pure ()
    pat_end
