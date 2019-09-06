def vpaddd1 : instruction :=
  definst "vpaddd" $ do
    pattern fun (v_3432 : reg (bv 128)) (v_3433 : reg (bv 128)) (v_3434 : reg (bv 128)) => do
      v_7207 <- getRegister v_3433;
      v_7209 <- getRegister v_3432;
      setRegister (lhs.of_reg v_3434) (concat (add (extract v_7207 0 32) (extract v_7209 0 32)) (concat (add (extract v_7207 32 64) (extract v_7209 32 64)) (concat (add (extract v_7207 64 96) (extract v_7209 64 96)) (add (extract v_7207 96 128) (extract v_7209 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3443 : reg (bv 256)) (v_3444 : reg (bv 256)) (v_3445 : reg (bv 256)) => do
      v_7230 <- getRegister v_3444;
      v_7232 <- getRegister v_3443;
      setRegister (lhs.of_reg v_3445) (concat (add (extract v_7230 0 32) (extract v_7232 0 32)) (concat (add (extract v_7230 32 64) (extract v_7232 32 64)) (concat (add (extract v_7230 64 96) (extract v_7232 64 96)) (concat (add (extract v_7230 96 128) (extract v_7232 96 128)) (concat (add (extract v_7230 128 160) (extract v_7232 128 160)) (concat (add (extract v_7230 160 192) (extract v_7232 160 192)) (concat (add (extract v_7230 192 224) (extract v_7232 192 224)) (add (extract v_7230 224 256) (extract v_7232 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3427 : Mem) (v_3428 : reg (bv 128)) (v_3429 : reg (bv 128)) => do
      v_12239 <- getRegister v_3428;
      v_12241 <- evaluateAddress v_3427;
      v_12242 <- load v_12241 16;
      setRegister (lhs.of_reg v_3429) (concat (add (extract v_12239 0 32) (extract v_12242 0 32)) (concat (add (extract v_12239 32 64) (extract v_12242 32 64)) (concat (add (extract v_12239 64 96) (extract v_12242 64 96)) (add (extract v_12239 96 128) (extract v_12242 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3438 : Mem) (v_3439 : reg (bv 256)) (v_3440 : reg (bv 256)) => do
      v_12258 <- getRegister v_3439;
      v_12260 <- evaluateAddress v_3438;
      v_12261 <- load v_12260 32;
      setRegister (lhs.of_reg v_3440) (concat (add (extract v_12258 0 32) (extract v_12261 0 32)) (concat (add (extract v_12258 32 64) (extract v_12261 32 64)) (concat (add (extract v_12258 64 96) (extract v_12261 64 96)) (concat (add (extract v_12258 96 128) (extract v_12261 96 128)) (concat (add (extract v_12258 128 160) (extract v_12261 128 160)) (concat (add (extract v_12258 160 192) (extract v_12261 160 192)) (concat (add (extract v_12258 192 224) (extract v_12261 192 224)) (add (extract v_12258 224 256) (extract v_12261 224 256)))))))));
      pure ()
    pat_end
