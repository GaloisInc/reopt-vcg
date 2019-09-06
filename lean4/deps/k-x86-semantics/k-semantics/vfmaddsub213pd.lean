def vfmaddsub213pd1 : instruction :=
  definst "vfmaddsub213pd" $ do
    pattern fun (v_2749 : reg (bv 128)) (v_2750 : reg (bv 128)) (v_2751 : reg (bv 128)) => do
      v_5064 <- getRegister v_2750;
      v_5067 <- getRegister v_2751;
      v_5071 <- getRegister v_2749;
      setRegister (lhs.of_reg v_2751) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5064 0 64) 53 11) (MInt2Float (extract v_5067 0 64) 53 11)) (MInt2Float (extract v_5071 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5064 64 128) 53 11) (MInt2Float (extract v_5067 64 128) 53 11)) (MInt2Float (extract v_5071 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2763 : reg (bv 256)) (v_2764 : reg (bv 256)) (v_2765 : reg (bv 256)) => do
      v_5092 <- getRegister v_2764;
      v_5095 <- getRegister v_2765;
      v_5099 <- getRegister v_2763;
      setRegister (lhs.of_reg v_2765) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5092 0 64) 53 11) (MInt2Float (extract v_5095 0 64) 53 11)) (MInt2Float (extract v_5099 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5092 64 128) 53 11) (MInt2Float (extract v_5095 64 128) 53 11)) (MInt2Float (extract v_5099 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5092 128 192) 53 11) (MInt2Float (extract v_5095 128 192) 53 11)) (MInt2Float (extract v_5099 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5092 192 256) 53 11) (MInt2Float (extract v_5095 192 256) 53 11)) (MInt2Float (extract v_5099 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) (v_2744 : reg (bv 128)) (v_2745 : reg (bv 128)) => do
      v_11004 <- getRegister v_2744;
      v_11007 <- getRegister v_2745;
      v_11011 <- evaluateAddress v_2746;
      v_11012 <- load v_11011 16;
      setRegister (lhs.of_reg v_2745) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11004 0 64) 53 11) (MInt2Float (extract v_11007 0 64) 53 11)) (MInt2Float (extract v_11012 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11004 64 128) 53 11) (MInt2Float (extract v_11007 64 128) 53 11)) (MInt2Float (extract v_11012 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2755 : Mem) (v_2758 : reg (bv 256)) (v_2759 : reg (bv 256)) => do
      v_11028 <- getRegister v_2758;
      v_11031 <- getRegister v_2759;
      v_11035 <- evaluateAddress v_2755;
      v_11036 <- load v_11035 32;
      setRegister (lhs.of_reg v_2759) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11028 0 64) 53 11) (MInt2Float (extract v_11031 0 64) 53 11)) (MInt2Float (extract v_11036 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11028 64 128) 53 11) (MInt2Float (extract v_11031 64 128) 53 11)) (MInt2Float (extract v_11036 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11028 128 192) 53 11) (MInt2Float (extract v_11031 128 192) 53 11)) (MInt2Float (extract v_11036 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11028 192 256) 53 11) (MInt2Float (extract v_11031 192 256) 53 11)) (MInt2Float (extract v_11036 192 256) 53 11)) 64)));
      pure ()
    pat_end
