def vfmsubadd213pd1 : instruction :=
  definst "vfmsubadd213pd" $ do
    pattern fun (v_2990 : reg (bv 128)) (v_2991 : reg (bv 128)) (v_2992 : reg (bv 128)) => do
      v_6350 <- getRegister v_2991;
      v_6353 <- getRegister v_2992;
      v_6357 <- getRegister v_2990;
      setRegister (lhs.of_reg v_2992) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6350 0 64) 53 11) (MInt2Float (extract v_6353 0 64) 53 11)) (MInt2Float (extract v_6357 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6350 64 128) 53 11) (MInt2Float (extract v_6353 64 128) 53 11)) (MInt2Float (extract v_6357 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3002 : reg (bv 256)) (v_3003 : reg (bv 256)) (v_3004 : reg (bv 256)) => do
      v_6378 <- getRegister v_3003;
      v_6381 <- getRegister v_3004;
      v_6385 <- getRegister v_3002;
      setRegister (lhs.of_reg v_3004) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6378 0 64) 53 11) (MInt2Float (extract v_6381 0 64) 53 11)) (MInt2Float (extract v_6385 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6378 64 128) 53 11) (MInt2Float (extract v_6381 64 128) 53 11)) (MInt2Float (extract v_6385 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6378 128 192) 53 11) (MInt2Float (extract v_6381 128 192) 53 11)) (MInt2Float (extract v_6385 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6378 192 256) 53 11) (MInt2Float (extract v_6381 192 256) 53 11)) (MInt2Float (extract v_6385 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2987 : Mem) (v_2985 : reg (bv 128)) (v_2986 : reg (bv 128)) => do
      v_12147 <- getRegister v_2985;
      v_12150 <- getRegister v_2986;
      v_12154 <- evaluateAddress v_2987;
      v_12155 <- load v_12154 16;
      setRegister (lhs.of_reg v_2986) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 0 64) 53 11) (MInt2Float (extract v_12150 0 64) 53 11)) (MInt2Float (extract v_12155 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12147 64 128) 53 11) (MInt2Float (extract v_12150 64 128) 53 11)) (MInt2Float (extract v_12155 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2996 : Mem) (v_2997 : reg (bv 256)) (v_2998 : reg (bv 256)) => do
      v_12171 <- getRegister v_2997;
      v_12174 <- getRegister v_2998;
      v_12178 <- evaluateAddress v_2996;
      v_12179 <- load v_12178 32;
      setRegister (lhs.of_reg v_2998) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12171 0 64) 53 11) (MInt2Float (extract v_12174 0 64) 53 11)) (MInt2Float (extract v_12179 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12171 64 128) 53 11) (MInt2Float (extract v_12174 64 128) 53 11)) (MInt2Float (extract v_12179 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12171 128 192) 53 11) (MInt2Float (extract v_12174 128 192) 53 11)) (MInt2Float (extract v_12179 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12171 192 256) 53 11) (MInt2Float (extract v_12174 192 256) 53 11)) (MInt2Float (extract v_12179 192 256) 53 11)) 64)));
      pure ()
    pat_end
