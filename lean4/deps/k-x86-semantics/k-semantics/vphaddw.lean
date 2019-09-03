def vphaddw1 : instruction :=
  definst "vphaddw" $ do
    pattern fun (v_3194 : reg (bv 128)) (v_3195 : reg (bv 128)) (v_3196 : reg (bv 128)) => do
      v_9347 <- getRegister v_3194;
      v_9363 <- getRegister v_3195;
      setRegister (lhs.of_reg v_3196) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9347 0 16) (extract v_9347 16 32)) (add (extract v_9347 32 48) (extract v_9347 48 64))) (add (extract v_9347 64 80) (extract v_9347 80 96))) (add (extract v_9347 96 112) (extract v_9347 112 128))) (add (extract v_9363 0 16) (extract v_9363 16 32))) (add (extract v_9363 32 48) (extract v_9363 48 64))) (add (extract v_9363 64 80) (extract v_9363 80 96))) (add (extract v_9363 96 112) (extract v_9363 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3205 : reg (bv 256)) (v_3206 : reg (bv 256)) (v_3207 : reg (bv 256)) => do
      v_9386 <- getRegister v_3205;
      v_9402 <- getRegister v_3206;
      setRegister (lhs.of_reg v_3207) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_9386 0 16) (extract v_9386 16 32)) (add (extract v_9386 32 48) (extract v_9386 48 64))) (add (extract v_9386 64 80) (extract v_9386 80 96))) (add (extract v_9386 96 112) (extract v_9386 112 128))) (add (extract v_9402 0 16) (extract v_9402 16 32))) (add (extract v_9402 32 48) (extract v_9402 48 64))) (add (extract v_9402 64 80) (extract v_9402 80 96))) (add (extract v_9402 96 112) (extract v_9402 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9386 128 144) (extract v_9386 144 160)) (add (extract v_9386 160 176) (extract v_9386 176 192))) (add (extract v_9386 192 208) (extract v_9386 208 224))) (add (extract v_9386 224 240) (extract v_9386 240 256))) (add (extract v_9402 128 144) (extract v_9402 144 160))) (add (extract v_9402 160 176) (extract v_9402 176 192))) (add (extract v_9402 192 208) (extract v_9402 208 224))) (add (extract v_9402 224 240) (extract v_9402 240 256))));
      pure ()
    pat_end;
    pattern fun (v_3188 : Mem) (v_3189 : reg (bv 128)) (v_3190 : reg (bv 128)) => do
      v_18359 <- evaluateAddress v_3188;
      v_18360 <- load v_18359 16;
      v_18376 <- getRegister v_3189;
      setRegister (lhs.of_reg v_3190) (concat (concat (concat (concat (concat (concat (concat (add (extract v_18360 0 16) (extract v_18360 16 32)) (add (extract v_18360 32 48) (extract v_18360 48 64))) (add (extract v_18360 64 80) (extract v_18360 80 96))) (add (extract v_18360 96 112) (extract v_18360 112 128))) (add (extract v_18376 0 16) (extract v_18376 16 32))) (add (extract v_18376 32 48) (extract v_18376 48 64))) (add (extract v_18376 64 80) (extract v_18376 80 96))) (add (extract v_18376 96 112) (extract v_18376 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3199 : Mem) (v_3200 : reg (bv 256)) (v_3201 : reg (bv 256)) => do
      v_18394 <- evaluateAddress v_3199;
      v_18395 <- load v_18394 32;
      v_18411 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3201) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_18395 0 16) (extract v_18395 16 32)) (add (extract v_18395 32 48) (extract v_18395 48 64))) (add (extract v_18395 64 80) (extract v_18395 80 96))) (add (extract v_18395 96 112) (extract v_18395 112 128))) (add (extract v_18411 0 16) (extract v_18411 16 32))) (add (extract v_18411 32 48) (extract v_18411 48 64))) (add (extract v_18411 64 80) (extract v_18411 80 96))) (add (extract v_18411 96 112) (extract v_18411 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_18395 128 144) (extract v_18395 144 160)) (add (extract v_18395 160 176) (extract v_18395 176 192))) (add (extract v_18395 192 208) (extract v_18395 208 224))) (add (extract v_18395 224 240) (extract v_18395 240 256))) (add (extract v_18411 128 144) (extract v_18411 144 160))) (add (extract v_18411 160 176) (extract v_18411 176 192))) (add (extract v_18411 192 208) (extract v_18411 208 224))) (add (extract v_18411 224 240) (extract v_18411 240 256))));
      pure ()
    pat_end
