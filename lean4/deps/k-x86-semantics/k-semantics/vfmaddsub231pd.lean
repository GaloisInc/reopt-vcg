def vfmaddsub231pd1 : instruction :=
  definst "vfmaddsub231pd" $ do
    pattern fun (v_2704 : reg (bv 128)) (v_2705 : reg (bv 128)) (v_2706 : reg (bv 128)) => do
      v_5182 <- getRegister v_2705;
      v_5185 <- getRegister v_2704;
      v_5189 <- getRegister v_2706;
      setRegister (lhs.of_reg v_2706) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5182 0 64) 53 11) (MInt2Float (extract v_5185 0 64) 53 11)) (MInt2Float (extract v_5189 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5182 64 128) 53 11) (MInt2Float (extract v_5185 64 128) 53 11)) (MInt2Float (extract v_5189 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2716 : reg (bv 256)) (v_2717 : reg (bv 256)) (v_2718 : reg (bv 256)) => do
      v_5210 <- getRegister v_2717;
      v_5213 <- getRegister v_2716;
      v_5217 <- getRegister v_2718;
      setRegister (lhs.of_reg v_2718) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5210 0 64) 53 11) (MInt2Float (extract v_5213 0 64) 53 11)) (MInt2Float (extract v_5217 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5210 64 128) 53 11) (MInt2Float (extract v_5213 64 128) 53 11)) (MInt2Float (extract v_5217 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5210 128 192) 53 11) (MInt2Float (extract v_5213 128 192) 53 11)) (MInt2Float (extract v_5217 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5210 192 256) 53 11) (MInt2Float (extract v_5213 192 256) 53 11)) (MInt2Float (extract v_5217 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2701 : Mem) (v_2699 : reg (bv 128)) (v_2700 : reg (bv 128)) => do
      v_11089 <- getRegister v_2699;
      v_11092 <- evaluateAddress v_2701;
      v_11093 <- load v_11092 16;
      v_11097 <- getRegister v_2700;
      setRegister (lhs.of_reg v_2700) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 0 64) 53 11) (MInt2Float (extract v_11093 0 64) 53 11)) (MInt2Float (extract v_11097 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11089 64 128) 53 11) (MInt2Float (extract v_11093 64 128) 53 11)) (MInt2Float (extract v_11097 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2710 : Mem) (v_2711 : reg (bv 256)) (v_2712 : reg (bv 256)) => do
      v_11113 <- getRegister v_2711;
      v_11116 <- evaluateAddress v_2710;
      v_11117 <- load v_11116 32;
      v_11121 <- getRegister v_2712;
      setRegister (lhs.of_reg v_2712) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11113 0 64) 53 11) (MInt2Float (extract v_11117 0 64) 53 11)) (MInt2Float (extract v_11121 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11113 64 128) 53 11) (MInt2Float (extract v_11117 64 128) 53 11)) (MInt2Float (extract v_11121 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11113 128 192) 53 11) (MInt2Float (extract v_11117 128 192) 53 11)) (MInt2Float (extract v_11121 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11113 192 256) 53 11) (MInt2Float (extract v_11117 192 256) 53 11)) (MInt2Float (extract v_11121 192 256) 53 11)) 64)));
      pure ()
    pat_end
