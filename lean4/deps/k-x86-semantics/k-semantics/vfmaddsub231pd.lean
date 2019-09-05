def vfmaddsub231pd1 : instruction :=
  definst "vfmaddsub231pd" $ do
    pattern fun (v_2769 : reg (bv 128)) (v_2770 : reg (bv 128)) (v_2771 : reg (bv 128)) => do
      v_5249 <- getRegister v_2770;
      v_5252 <- getRegister v_2769;
      v_5256 <- getRegister v_2771;
      setRegister (lhs.of_reg v_2771) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5249 0 64) 53 11) (MInt2Float (extract v_5252 0 64) 53 11)) (MInt2Float (extract v_5256 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5249 64 128) 53 11) (MInt2Float (extract v_5252 64 128) 53 11)) (MInt2Float (extract v_5256 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2779 : reg (bv 256)) (v_2780 : reg (bv 256)) (v_2781 : reg (bv 256)) => do
      v_5277 <- getRegister v_2780;
      v_5280 <- getRegister v_2779;
      v_5284 <- getRegister v_2781;
      setRegister (lhs.of_reg v_2781) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5277 0 64) 53 11) (MInt2Float (extract v_5280 0 64) 53 11)) (MInt2Float (extract v_5284 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5277 64 128) 53 11) (MInt2Float (extract v_5280 64 128) 53 11)) (MInt2Float (extract v_5284 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5277 128 192) 53 11) (MInt2Float (extract v_5280 128 192) 53 11)) (MInt2Float (extract v_5284 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5277 192 256) 53 11) (MInt2Float (extract v_5280 192 256) 53 11)) (MInt2Float (extract v_5284 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2763 : Mem) (v_2764 : reg (bv 128)) (v_2765 : reg (bv 128)) => do
      v_11173 <- getRegister v_2764;
      v_11176 <- evaluateAddress v_2763;
      v_11177 <- load v_11176 16;
      v_11181 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2765) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11173 0 64) 53 11) (MInt2Float (extract v_11177 0 64) 53 11)) (MInt2Float (extract v_11181 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11173 64 128) 53 11) (MInt2Float (extract v_11177 64 128) 53 11)) (MInt2Float (extract v_11181 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2774 : Mem) (v_2775 : reg (bv 256)) (v_2776 : reg (bv 256)) => do
      v_11197 <- getRegister v_2775;
      v_11200 <- evaluateAddress v_2774;
      v_11201 <- load v_11200 32;
      v_11205 <- getRegister v_2776;
      setRegister (lhs.of_reg v_2776) (concat (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11197 0 64) 53 11) (MInt2Float (extract v_11201 0 64) 53 11)) (MInt2Float (extract v_11205 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11197 64 128) 53 11) (MInt2Float (extract v_11201 64 128) 53 11)) (MInt2Float (extract v_11205 64 128) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11197 128 192) 53 11) (MInt2Float (extract v_11201 128 192) 53 11)) (MInt2Float (extract v_11205 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11197 192 256) 53 11) (MInt2Float (extract v_11201 192 256) 53 11)) (MInt2Float (extract v_11205 192 256) 53 11)) 64)));
      pure ()
    pat_end
