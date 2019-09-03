def vhaddpd1 : instruction :=
  definst "vhaddpd" $ do
    pattern fun (v_3474 : reg (bv 128)) (v_3475 : reg (bv 128)) (v_3476 : reg (bv 128)) => do
      v_8070 <- getRegister v_3474;
      v_8077 <- getRegister v_3475;
      setRegister (lhs.of_reg v_3476) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8070 64 128) 53 11) (MInt2Float (extract v_8070 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8077 64 128) 53 11) (MInt2Float (extract v_8077 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3486 : reg (bv 256)) (v_3487 : reg (bv 256)) (v_3488 : reg (bv 256)) => do
      v_8091 <- getRegister v_3486;
      v_8098 <- getRegister v_3487;
      setRegister (lhs.of_reg v_3488) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8091 64 128) 53 11) (MInt2Float (extract v_8091 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8098 64 128) 53 11) (MInt2Float (extract v_8098 0 64) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8091 192 256) 53 11) (MInt2Float (extract v_8091 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8098 192 256) 53 11) (MInt2Float (extract v_8098 128 192) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3471 : Mem) (v_3469 : reg (bv 128)) (v_3470 : reg (bv 128)) => do
      v_13679 <- evaluateAddress v_3471;
      v_13680 <- load v_13679 16;
      v_13687 <- getRegister v_3469;
      setRegister (lhs.of_reg v_3470) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13680 64 128) 53 11) (MInt2Float (extract v_13680 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13687 64 128) 53 11) (MInt2Float (extract v_13687 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3480 : Mem) (v_3481 : reg (bv 256)) (v_3482 : reg (bv 256)) => do
      v_13696 <- evaluateAddress v_3480;
      v_13697 <- load v_13696 32;
      v_13704 <- getRegister v_3481;
      setRegister (lhs.of_reg v_3482) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13697 64 128) 53 11) (MInt2Float (extract v_13697 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13704 64 128) 53 11) (MInt2Float (extract v_13704 0 64) 53 11)) 64)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13697 192 256) 53 11) (MInt2Float (extract v_13697 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_13704 192 256) 53 11) (MInt2Float (extract v_13704 128 192) 53 11)) 64)));
      pure ()
    pat_end
