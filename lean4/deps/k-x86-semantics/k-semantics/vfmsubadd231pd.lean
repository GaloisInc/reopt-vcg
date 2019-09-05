def vfmsubadd231pd1 : instruction :=
  definst "vfmsubadd231pd" $ do
    pattern fun (v_3099 : reg (bv 128)) (v_3100 : reg (bv 128)) (v_3101 : reg (bv 128)) => do
      v_6629 <- getRegister v_3100;
      v_6632 <- getRegister v_3099;
      v_6636 <- getRegister v_3101;
      setRegister (lhs.of_reg v_3101) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6629 0 64) 53 11) (MInt2Float (extract v_6632 0 64) 53 11)) (MInt2Float (extract v_6636 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6629 64 128) 53 11) (MInt2Float (extract v_6632 64 128) 53 11)) (MInt2Float (extract v_6636 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3109 : reg (bv 256)) (v_3110 : reg (bv 256)) (v_3111 : reg (bv 256)) => do
      v_6657 <- getRegister v_3110;
      v_6660 <- getRegister v_3109;
      v_6664 <- getRegister v_3111;
      setRegister (lhs.of_reg v_3111) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6657 0 64) 53 11) (MInt2Float (extract v_6660 0 64) 53 11)) (MInt2Float (extract v_6664 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6657 64 128) 53 11) (MInt2Float (extract v_6660 64 128) 53 11)) (MInt2Float (extract v_6664 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6657 128 192) 53 11) (MInt2Float (extract v_6660 128 192) 53 11)) (MInt2Float (extract v_6664 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6657 192 256) 53 11) (MInt2Float (extract v_6660 192 256) 53 11)) (MInt2Float (extract v_6664 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3093 : Mem) (v_3094 : reg (bv 128)) (v_3095 : reg (bv 128)) => do
      v_12427 <- getRegister v_3094;
      v_12430 <- evaluateAddress v_3093;
      v_12431 <- load v_12430 16;
      v_12435 <- getRegister v_3095;
      setRegister (lhs.of_reg v_3095) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12427 0 64) 53 11) (MInt2Float (extract v_12431 0 64) 53 11)) (MInt2Float (extract v_12435 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12427 64 128) 53 11) (MInt2Float (extract v_12431 64 128) 53 11)) (MInt2Float (extract v_12435 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3104 : Mem) (v_3105 : reg (bv 256)) (v_3106 : reg (bv 256)) => do
      v_12451 <- getRegister v_3105;
      v_12454 <- evaluateAddress v_3104;
      v_12455 <- load v_12454 32;
      v_12459 <- getRegister v_3106;
      setRegister (lhs.of_reg v_3106) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12451 0 64) 53 11) (MInt2Float (extract v_12455 0 64) 53 11)) (MInt2Float (extract v_12459 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12451 64 128) 53 11) (MInt2Float (extract v_12455 64 128) 53 11)) (MInt2Float (extract v_12459 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12451 128 192) 53 11) (MInt2Float (extract v_12455 128 192) 53 11)) (MInt2Float (extract v_12459 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12451 192 256) 53 11) (MInt2Float (extract v_12455 192 256) 53 11)) (MInt2Float (extract v_12459 192 256) 53 11)) 64)));
      pure ()
    pat_end
