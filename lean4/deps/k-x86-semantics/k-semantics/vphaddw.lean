def vphaddw1 : instruction :=
  definst "vphaddw" $ do
    pattern fun (v_3284 : reg (bv 128)) (v_3285 : reg (bv 128)) (v_3286 : reg (bv 128)) => do
      v_9030 <- getRegister v_3284;
      v_9046 <- getRegister v_3285;
      setRegister (lhs.of_reg v_3286) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9030 0 16) (extract v_9030 16 32)) (add (extract v_9030 32 48) (extract v_9030 48 64))) (add (extract v_9030 64 80) (extract v_9030 80 96))) (add (extract v_9030 96 112) (extract v_9030 112 128))) (add (extract v_9046 0 16) (extract v_9046 16 32))) (add (extract v_9046 32 48) (extract v_9046 48 64))) (add (extract v_9046 64 80) (extract v_9046 80 96))) (add (extract v_9046 96 112) (extract v_9046 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3295 : reg (bv 256)) (v_3296 : reg (bv 256)) (v_3297 : reg (bv 256)) => do
      v_9069 <- getRegister v_3295;
      v_9085 <- getRegister v_3296;
      setRegister (lhs.of_reg v_3297) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_9069 0 16) (extract v_9069 16 32)) (add (extract v_9069 32 48) (extract v_9069 48 64))) (add (extract v_9069 64 80) (extract v_9069 80 96))) (add (extract v_9069 96 112) (extract v_9069 112 128))) (add (extract v_9085 0 16) (extract v_9085 16 32))) (add (extract v_9085 32 48) (extract v_9085 48 64))) (add (extract v_9085 64 80) (extract v_9085 80 96))) (add (extract v_9085 96 112) (extract v_9085 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_9069 128 144) (extract v_9069 144 160)) (add (extract v_9069 160 176) (extract v_9069 176 192))) (add (extract v_9069 192 208) (extract v_9069 208 224))) (add (extract v_9069 224 240) (extract v_9069 240 256))) (add (extract v_9085 128 144) (extract v_9085 144 160))) (add (extract v_9085 160 176) (extract v_9085 176 192))) (add (extract v_9085 192 208) (extract v_9085 208 224))) (add (extract v_9085 224 240) (extract v_9085 240 256))));
      pure ()
    pat_end;
    pattern fun (v_3279 : Mem) (v_3280 : reg (bv 128)) (v_3281 : reg (bv 128)) => do
      v_17434 <- evaluateAddress v_3279;
      v_17435 <- load v_17434 16;
      v_17451 <- getRegister v_3280;
      setRegister (lhs.of_reg v_3281) (concat (concat (concat (concat (concat (concat (concat (add (extract v_17435 0 16) (extract v_17435 16 32)) (add (extract v_17435 32 48) (extract v_17435 48 64))) (add (extract v_17435 64 80) (extract v_17435 80 96))) (add (extract v_17435 96 112) (extract v_17435 112 128))) (add (extract v_17451 0 16) (extract v_17451 16 32))) (add (extract v_17451 32 48) (extract v_17451 48 64))) (add (extract v_17451 64 80) (extract v_17451 80 96))) (add (extract v_17451 96 112) (extract v_17451 112 128)));
      pure ()
    pat_end;
    pattern fun (v_3290 : Mem) (v_3291 : reg (bv 256)) (v_3292 : reg (bv 256)) => do
      v_17469 <- evaluateAddress v_3290;
      v_17470 <- load v_17469 32;
      v_17486 <- getRegister v_3291;
      setRegister (lhs.of_reg v_3292) (concat (concat (concat (concat (concat (concat (concat (concat (add (extract v_17470 0 16) (extract v_17470 16 32)) (add (extract v_17470 32 48) (extract v_17470 48 64))) (add (extract v_17470 64 80) (extract v_17470 80 96))) (add (extract v_17470 96 112) (extract v_17470 112 128))) (add (extract v_17486 0 16) (extract v_17486 16 32))) (add (extract v_17486 32 48) (extract v_17486 48 64))) (add (extract v_17486 64 80) (extract v_17486 80 96))) (add (extract v_17486 96 112) (extract v_17486 112 128))) (concat (concat (concat (concat (concat (concat (concat (add (extract v_17470 128 144) (extract v_17470 144 160)) (add (extract v_17470 160 176) (extract v_17470 176 192))) (add (extract v_17470 192 208) (extract v_17470 208 224))) (add (extract v_17470 224 240) (extract v_17470 240 256))) (add (extract v_17486 128 144) (extract v_17486 144 160))) (add (extract v_17486 160 176) (extract v_17486 176 192))) (add (extract v_17486 192 208) (extract v_17486 208 224))) (add (extract v_17486 224 240) (extract v_17486 240 256))));
      pure ()
    pat_end
