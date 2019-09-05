def vdivps1 : instruction :=
  definst "vdivps" $ do
    pattern fun (v_3433 : reg (bv 128)) (v_3434 : reg (bv 128)) (v_3435 : reg (bv 128)) => do
      v_6405 <- getRegister v_3434;
      v_6408 <- getRegister v_3433;
      setRegister (lhs.of_reg v_3435) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6405 0 32) 24 8) (MInt2Float (extract v_6408 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6405 32 64) 24 8) (MInt2Float (extract v_6408 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6405 64 96) 24 8) (MInt2Float (extract v_6408 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6405 96 128) 24 8) (MInt2Float (extract v_6408 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3443 : reg (bv 256)) (v_3444 : reg (bv 256)) (v_3445 : reg (bv 256)) => do
      v_6440 <- getRegister v_3444;
      v_6443 <- getRegister v_3443;
      setRegister (lhs.of_reg v_3445) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 0 32) 24 8) (MInt2Float (extract v_6443 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 32 64) 24 8) (MInt2Float (extract v_6443 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 64 96) 24 8) (MInt2Float (extract v_6443 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 96 128) 24 8) (MInt2Float (extract v_6443 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 128 160) 24 8) (MInt2Float (extract v_6443 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 160 192) 24 8) (MInt2Float (extract v_6443 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 192 224) 24 8) (MInt2Float (extract v_6443 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6440 224 256) 24 8) (MInt2Float (extract v_6443 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3427 : Mem) (v_3428 : reg (bv 128)) (v_3429 : reg (bv 128)) => do
      v_10409 <- getRegister v_3428;
      v_10412 <- evaluateAddress v_3427;
      v_10413 <- load v_10412 16;
      setRegister (lhs.of_reg v_3429) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10409 0 32) 24 8) (MInt2Float (extract v_10413 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10409 32 64) 24 8) (MInt2Float (extract v_10413 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10409 64 96) 24 8) (MInt2Float (extract v_10413 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10409 96 128) 24 8) (MInt2Float (extract v_10413 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3438 : Mem) (v_3439 : reg (bv 256)) (v_3440 : reg (bv 256)) => do
      v_10440 <- getRegister v_3439;
      v_10443 <- evaluateAddress v_3438;
      v_10444 <- load v_10443 32;
      setRegister (lhs.of_reg v_3440) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 0 32) 24 8) (MInt2Float (extract v_10444 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 32 64) 24 8) (MInt2Float (extract v_10444 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 64 96) 24 8) (MInt2Float (extract v_10444 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 96 128) 24 8) (MInt2Float (extract v_10444 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 128 160) 24 8) (MInt2Float (extract v_10444 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 160 192) 24 8) (MInt2Float (extract v_10444 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 192 224) 24 8) (MInt2Float (extract v_10444 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10440 224 256) 24 8) (MInt2Float (extract v_10444 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
