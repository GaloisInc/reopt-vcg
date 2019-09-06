def vfmaddsub231pd1 : instruction :=
  definst "vfmaddsub231pd" $ do
    pattern fun (v_2793 : reg (bv 128)) (v_2794 : reg (bv 128)) (v_2795 : reg (bv 128)) => do
      v_5276 <- getRegister v_2794;
      v_5279 <- getRegister v_2793;
      v_5283 <- getRegister v_2795;
      setRegister (lhs.of_reg v_2795) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5276 0 64) 53 11) (MInt2Float (extract v_5279 0 64) 53 11)) (MInt2Float (extract v_5283 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5276 64 128) 53 11) (MInt2Float (extract v_5279 64 128) 53 11)) (MInt2Float (extract v_5283 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2807 : reg (bv 256)) (v_2808 : reg (bv 256)) (v_2809 : reg (bv 256)) => do
      v_5304 <- getRegister v_2808;
      v_5307 <- getRegister v_2807;
      v_5311 <- getRegister v_2809;
      setRegister (lhs.of_reg v_2809) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5304 0 64) 53 11) (MInt2Float (extract v_5307 0 64) 53 11)) (MInt2Float (extract v_5311 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5304 64 128) 53 11) (MInt2Float (extract v_5307 64 128) 53 11)) (MInt2Float (extract v_5311 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5304 128 192) 53 11) (MInt2Float (extract v_5307 128 192) 53 11)) (MInt2Float (extract v_5311 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5304 192 256) 53 11) (MInt2Float (extract v_5307 192 256) 53 11)) (MInt2Float (extract v_5311 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2790 : Mem) (v_2788 : reg (bv 128)) (v_2789 : reg (bv 128)) => do
      v_11200 <- getRegister v_2788;
      v_11203 <- evaluateAddress v_2790;
      v_11204 <- load v_11203 16;
      v_11208 <- getRegister v_2789;
      setRegister (lhs.of_reg v_2789) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11200 0 64) 53 11) (MInt2Float (extract v_11204 0 64) 53 11)) (MInt2Float (extract v_11208 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11200 64 128) 53 11) (MInt2Float (extract v_11204 64 128) 53 11)) (MInt2Float (extract v_11208 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2799 : Mem) (v_2802 : reg (bv 256)) (v_2803 : reg (bv 256)) => do
      v_11224 <- getRegister v_2802;
      v_11227 <- evaluateAddress v_2799;
      v_11228 <- load v_11227 32;
      v_11232 <- getRegister v_2803;
      setRegister (lhs.of_reg v_2803) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11224 0 64) 53 11) (MInt2Float (extract v_11228 0 64) 53 11)) (MInt2Float (extract v_11232 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11224 64 128) 53 11) (MInt2Float (extract v_11228 64 128) 53 11)) (MInt2Float (extract v_11232 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11224 128 192) 53 11) (MInt2Float (extract v_11228 128 192) 53 11)) (MInt2Float (extract v_11232 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11224 192 256) 53 11) (MInt2Float (extract v_11228 192 256) 53 11)) (MInt2Float (extract v_11232 192 256) 53 11)) 64)));
      pure ()
    pat_end
