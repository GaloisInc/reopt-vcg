def vpaddusw1 : instruction :=
  definst "vpaddusw" $ do
    pattern fun (v_2516 : reg (bv 128)) (v_2517 : reg (bv 128)) (v_2518 : reg (bv 128)) => do
      v_5329 <- getRegister v_2517;
      v_5332 <- getRegister v_2516;
      v_5335 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 0 16)) (concat (expression.bv_nat 1 0) (extract v_5332 0 16)));
      v_5343 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 16 32)) (concat (expression.bv_nat 1 0) (extract v_5332 16 32)));
      v_5351 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 32 48)) (concat (expression.bv_nat 1 0) (extract v_5332 32 48)));
      v_5359 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 48 64)) (concat (expression.bv_nat 1 0) (extract v_5332 48 64)));
      v_5367 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 64 80)) (concat (expression.bv_nat 1 0) (extract v_5332 64 80)));
      v_5375 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 80 96)) (concat (expression.bv_nat 1 0) (extract v_5332 80 96)));
      v_5383 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 96 112)) (concat (expression.bv_nat 1 0) (extract v_5332 96 112)));
      v_5391 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5329 112 128)) (concat (expression.bv_nat 1 0) (extract v_5332 112 128)));
      setRegister (lhs.of_reg v_2518) (concat (mux (isBitSet v_5335 0) (expression.bv_nat 16 65535) (extract v_5335 1 17)) (concat (mux (isBitSet v_5343 0) (expression.bv_nat 16 65535) (extract v_5343 1 17)) (concat (mux (isBitSet v_5351 0) (expression.bv_nat 16 65535) (extract v_5351 1 17)) (concat (mux (isBitSet v_5359 0) (expression.bv_nat 16 65535) (extract v_5359 1 17)) (concat (mux (isBitSet v_5367 0) (expression.bv_nat 16 65535) (extract v_5367 1 17)) (concat (mux (isBitSet v_5375 0) (expression.bv_nat 16 65535) (extract v_5375 1 17)) (concat (mux (isBitSet v_5383 0) (expression.bv_nat 16 65535) (extract v_5383 1 17)) (mux (isBitSet v_5391 0) (expression.bv_nat 16 65535) (extract v_5391 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2526 : reg (bv 256)) (v_2527 : reg (bv 256)) (v_2528 : reg (bv 256)) => do
      v_5408 <- getRegister v_2527;
      v_5411 <- getRegister v_2526;
      v_5414 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 0 16)) (concat (expression.bv_nat 1 0) (extract v_5411 0 16)));
      v_5422 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 16 32)) (concat (expression.bv_nat 1 0) (extract v_5411 16 32)));
      v_5430 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 32 48)) (concat (expression.bv_nat 1 0) (extract v_5411 32 48)));
      v_5438 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 48 64)) (concat (expression.bv_nat 1 0) (extract v_5411 48 64)));
      v_5446 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 64 80)) (concat (expression.bv_nat 1 0) (extract v_5411 64 80)));
      v_5454 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 80 96)) (concat (expression.bv_nat 1 0) (extract v_5411 80 96)));
      v_5462 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 96 112)) (concat (expression.bv_nat 1 0) (extract v_5411 96 112)));
      v_5470 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 112 128)) (concat (expression.bv_nat 1 0) (extract v_5411 112 128)));
      v_5478 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 128 144)) (concat (expression.bv_nat 1 0) (extract v_5411 128 144)));
      v_5486 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 144 160)) (concat (expression.bv_nat 1 0) (extract v_5411 144 160)));
      v_5494 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 160 176)) (concat (expression.bv_nat 1 0) (extract v_5411 160 176)));
      v_5502 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 176 192)) (concat (expression.bv_nat 1 0) (extract v_5411 176 192)));
      v_5510 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 192 208)) (concat (expression.bv_nat 1 0) (extract v_5411 192 208)));
      v_5518 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 208 224)) (concat (expression.bv_nat 1 0) (extract v_5411 208 224)));
      v_5526 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 224 240)) (concat (expression.bv_nat 1 0) (extract v_5411 224 240)));
      v_5534 <- eval (add (concat (expression.bv_nat 1 0) (extract v_5408 240 256)) (concat (expression.bv_nat 1 0) (extract v_5411 240 256)));
      setRegister (lhs.of_reg v_2528) (concat (mux (isBitSet v_5414 0) (expression.bv_nat 16 65535) (extract v_5414 1 17)) (concat (mux (isBitSet v_5422 0) (expression.bv_nat 16 65535) (extract v_5422 1 17)) (concat (mux (isBitSet v_5430 0) (expression.bv_nat 16 65535) (extract v_5430 1 17)) (concat (mux (isBitSet v_5438 0) (expression.bv_nat 16 65535) (extract v_5438 1 17)) (concat (mux (isBitSet v_5446 0) (expression.bv_nat 16 65535) (extract v_5446 1 17)) (concat (mux (isBitSet v_5454 0) (expression.bv_nat 16 65535) (extract v_5454 1 17)) (concat (mux (isBitSet v_5462 0) (expression.bv_nat 16 65535) (extract v_5462 1 17)) (concat (mux (isBitSet v_5470 0) (expression.bv_nat 16 65535) (extract v_5470 1 17)) (concat (mux (isBitSet v_5478 0) (expression.bv_nat 16 65535) (extract v_5478 1 17)) (concat (mux (isBitSet v_5486 0) (expression.bv_nat 16 65535) (extract v_5486 1 17)) (concat (mux (isBitSet v_5494 0) (expression.bv_nat 16 65535) (extract v_5494 1 17)) (concat (mux (isBitSet v_5502 0) (expression.bv_nat 16 65535) (extract v_5502 1 17)) (concat (mux (isBitSet v_5510 0) (expression.bv_nat 16 65535) (extract v_5510 1 17)) (concat (mux (isBitSet v_5518 0) (expression.bv_nat 16 65535) (extract v_5518 1 17)) (concat (mux (isBitSet v_5526 0) (expression.bv_nat 16 65535) (extract v_5526 1 17)) (mux (isBitSet v_5534 0) (expression.bv_nat 16 65535) (extract v_5534 1 17)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2510 : Mem) (v_2511 : reg (bv 128)) (v_2512 : reg (bv 128)) => do
      v_14065 <- getRegister v_2511;
      v_14068 <- evaluateAddress v_2510;
      v_14069 <- load v_14068 16;
      v_14072 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 0 16)) (concat (expression.bv_nat 1 0) (extract v_14069 0 16)));
      v_14080 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 16 32)) (concat (expression.bv_nat 1 0) (extract v_14069 16 32)));
      v_14088 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 32 48)) (concat (expression.bv_nat 1 0) (extract v_14069 32 48)));
      v_14096 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 48 64)) (concat (expression.bv_nat 1 0) (extract v_14069 48 64)));
      v_14104 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 64 80)) (concat (expression.bv_nat 1 0) (extract v_14069 64 80)));
      v_14112 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 80 96)) (concat (expression.bv_nat 1 0) (extract v_14069 80 96)));
      v_14120 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 96 112)) (concat (expression.bv_nat 1 0) (extract v_14069 96 112)));
      v_14128 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14065 112 128)) (concat (expression.bv_nat 1 0) (extract v_14069 112 128)));
      setRegister (lhs.of_reg v_2512) (concat (mux (isBitSet v_14072 0) (expression.bv_nat 16 65535) (extract v_14072 1 17)) (concat (mux (isBitSet v_14080 0) (expression.bv_nat 16 65535) (extract v_14080 1 17)) (concat (mux (isBitSet v_14088 0) (expression.bv_nat 16 65535) (extract v_14088 1 17)) (concat (mux (isBitSet v_14096 0) (expression.bv_nat 16 65535) (extract v_14096 1 17)) (concat (mux (isBitSet v_14104 0) (expression.bv_nat 16 65535) (extract v_14104 1 17)) (concat (mux (isBitSet v_14112 0) (expression.bv_nat 16 65535) (extract v_14112 1 17)) (concat (mux (isBitSet v_14120 0) (expression.bv_nat 16 65535) (extract v_14120 1 17)) (mux (isBitSet v_14128 0) (expression.bv_nat 16 65535) (extract v_14128 1 17)))))))));
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2522 : reg (bv 256)) (v_2523 : reg (bv 256)) => do
      v_14140 <- getRegister v_2522;
      v_14143 <- evaluateAddress v_2521;
      v_14144 <- load v_14143 32;
      v_14147 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 0 16)) (concat (expression.bv_nat 1 0) (extract v_14144 0 16)));
      v_14155 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 16 32)) (concat (expression.bv_nat 1 0) (extract v_14144 16 32)));
      v_14163 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 32 48)) (concat (expression.bv_nat 1 0) (extract v_14144 32 48)));
      v_14171 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 48 64)) (concat (expression.bv_nat 1 0) (extract v_14144 48 64)));
      v_14179 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 64 80)) (concat (expression.bv_nat 1 0) (extract v_14144 64 80)));
      v_14187 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 80 96)) (concat (expression.bv_nat 1 0) (extract v_14144 80 96)));
      v_14195 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 96 112)) (concat (expression.bv_nat 1 0) (extract v_14144 96 112)));
      v_14203 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 112 128)) (concat (expression.bv_nat 1 0) (extract v_14144 112 128)));
      v_14211 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 128 144)) (concat (expression.bv_nat 1 0) (extract v_14144 128 144)));
      v_14219 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 144 160)) (concat (expression.bv_nat 1 0) (extract v_14144 144 160)));
      v_14227 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 160 176)) (concat (expression.bv_nat 1 0) (extract v_14144 160 176)));
      v_14235 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 176 192)) (concat (expression.bv_nat 1 0) (extract v_14144 176 192)));
      v_14243 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 192 208)) (concat (expression.bv_nat 1 0) (extract v_14144 192 208)));
      v_14251 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 208 224)) (concat (expression.bv_nat 1 0) (extract v_14144 208 224)));
      v_14259 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 224 240)) (concat (expression.bv_nat 1 0) (extract v_14144 224 240)));
      v_14267 <- eval (add (concat (expression.bv_nat 1 0) (extract v_14140 240 256)) (concat (expression.bv_nat 1 0) (extract v_14144 240 256)));
      setRegister (lhs.of_reg v_2523) (concat (mux (isBitSet v_14147 0) (expression.bv_nat 16 65535) (extract v_14147 1 17)) (concat (mux (isBitSet v_14155 0) (expression.bv_nat 16 65535) (extract v_14155 1 17)) (concat (mux (isBitSet v_14163 0) (expression.bv_nat 16 65535) (extract v_14163 1 17)) (concat (mux (isBitSet v_14171 0) (expression.bv_nat 16 65535) (extract v_14171 1 17)) (concat (mux (isBitSet v_14179 0) (expression.bv_nat 16 65535) (extract v_14179 1 17)) (concat (mux (isBitSet v_14187 0) (expression.bv_nat 16 65535) (extract v_14187 1 17)) (concat (mux (isBitSet v_14195 0) (expression.bv_nat 16 65535) (extract v_14195 1 17)) (concat (mux (isBitSet v_14203 0) (expression.bv_nat 16 65535) (extract v_14203 1 17)) (concat (mux (isBitSet v_14211 0) (expression.bv_nat 16 65535) (extract v_14211 1 17)) (concat (mux (isBitSet v_14219 0) (expression.bv_nat 16 65535) (extract v_14219 1 17)) (concat (mux (isBitSet v_14227 0) (expression.bv_nat 16 65535) (extract v_14227 1 17)) (concat (mux (isBitSet v_14235 0) (expression.bv_nat 16 65535) (extract v_14235 1 17)) (concat (mux (isBitSet v_14243 0) (expression.bv_nat 16 65535) (extract v_14243 1 17)) (concat (mux (isBitSet v_14251 0) (expression.bv_nat 16 65535) (extract v_14251 1 17)) (concat (mux (isBitSet v_14259 0) (expression.bv_nat 16 65535) (extract v_14259 1 17)) (mux (isBitSet v_14267 0) (expression.bv_nat 16 65535) (extract v_14267 1 17)))))))))))))))));
      pure ()
    pat_end
