def vhaddps1 : instruction :=
  definst "vhaddps" $ do
    pattern fun (v_2386 : reg (bv 128)) (v_2387 : reg (bv 128)) (v_2388 : reg (bv 128)) => do
      v_3931 <- getRegister v_2386;
      v_3945 <- getRegister v_2387;
      setRegister (lhs.of_reg v_2388) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3931 32 64) 24 8) (MInt2Float (extract v_3931 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3931 96 128) 24 8) (MInt2Float (extract v_3931 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3945 32 64) 24 8) (MInt2Float (extract v_3945 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3945 96 128) 24 8) (MInt2Float (extract v_3945 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2397 : reg (bv 256)) (v_2398 : reg (bv 256)) (v_2399 : reg (bv 256)) => do
      v_3966 <- getRegister v_2397;
      v_3980 <- getRegister v_2398;
      setRegister (lhs.of_reg v_2399) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3966 32 64) 24 8) (MInt2Float (extract v_3966 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3966 96 128) 24 8) (MInt2Float (extract v_3966 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3980 32 64) 24 8) (MInt2Float (extract v_3980 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3980 96 128) 24 8) (MInt2Float (extract v_3980 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3966 160 192) 24 8) (MInt2Float (extract v_3966 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3966 224 256) 24 8) (MInt2Float (extract v_3966 192 224) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3980 160 192) 24 8) (MInt2Float (extract v_3980 128 160) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3980 224 256) 24 8) (MInt2Float (extract v_3980 192 224) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2380 : Mem) (v_2381 : reg (bv 128)) (v_2382 : reg (bv 128)) => do
      v_9577 <- evaluateAddress v_2380;
      v_9578 <- load v_9577 16;
      v_9592 <- getRegister v_2381;
      setRegister (lhs.of_reg v_2382) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9578 32 64) 24 8) (MInt2Float (extract v_9578 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9578 96 128) 24 8) (MInt2Float (extract v_9578 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9592 32 64) 24 8) (MInt2Float (extract v_9592 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9592 96 128) 24 8) (MInt2Float (extract v_9592 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2391 : Mem) (v_2392 : reg (bv 256)) (v_2393 : reg (bv 256)) => do
      v_9608 <- evaluateAddress v_2391;
      v_9609 <- load v_9608 32;
      v_9623 <- getRegister v_2392;
      setRegister (lhs.of_reg v_2393) (concat (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9609 32 64) 24 8) (MInt2Float (extract v_9609 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9609 96 128) 24 8) (MInt2Float (extract v_9609 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9623 32 64) 24 8) (MInt2Float (extract v_9623 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9623 96 128) 24 8) (MInt2Float (extract v_9623 64 96) 24 8)) 32)) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9609 160 192) 24 8) (MInt2Float (extract v_9609 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9609 224 256) 24 8) (MInt2Float (extract v_9609 192 224) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9623 160 192) 24 8) (MInt2Float (extract v_9623 128 160) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9623 224 256) 24 8) (MInt2Float (extract v_9623 192 224) 24 8)) 32)));
      pure ()
    pat_end
