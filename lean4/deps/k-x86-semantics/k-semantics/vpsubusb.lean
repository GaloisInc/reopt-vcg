def vpsubusb1 : instruction :=
  definst "vpsubusb" $ do
    pattern fun (v_2587 : reg (bv 128)) (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_5132 <- getRegister v_2588;
      v_5135 <- getRegister v_2587;
      v_5138 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 0 8)) (concat (expression.bv_nat 2 0) (extract v_5135 0 8)));
      v_5148 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 8 16)) (concat (expression.bv_nat 2 0) (extract v_5135 8 16)));
      v_5158 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 16 24)) (concat (expression.bv_nat 2 0) (extract v_5135 16 24)));
      v_5168 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 24 32)) (concat (expression.bv_nat 2 0) (extract v_5135 24 32)));
      v_5178 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 32 40)) (concat (expression.bv_nat 2 0) (extract v_5135 32 40)));
      v_5188 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 40 48)) (concat (expression.bv_nat 2 0) (extract v_5135 40 48)));
      v_5198 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 48 56)) (concat (expression.bv_nat 2 0) (extract v_5135 48 56)));
      v_5208 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 56 64)) (concat (expression.bv_nat 2 0) (extract v_5135 56 64)));
      v_5218 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 64 72)) (concat (expression.bv_nat 2 0) (extract v_5135 64 72)));
      v_5228 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 72 80)) (concat (expression.bv_nat 2 0) (extract v_5135 72 80)));
      v_5238 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 80 88)) (concat (expression.bv_nat 2 0) (extract v_5135 80 88)));
      v_5248 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 88 96)) (concat (expression.bv_nat 2 0) (extract v_5135 88 96)));
      v_5258 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 96 104)) (concat (expression.bv_nat 2 0) (extract v_5135 96 104)));
      v_5268 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 104 112)) (concat (expression.bv_nat 2 0) (extract v_5135 104 112)));
      v_5278 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 112 120)) (concat (expression.bv_nat 2 0) (extract v_5135 112 120)));
      v_5288 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5132 120 128)) (concat (expression.bv_nat 2 0) (extract v_5135 120 128)));
      setRegister (lhs.of_reg v_2589) (concat (mux (sgt v_5138 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5138 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5138 2 10))) (concat (mux (sgt v_5148 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5148 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5148 2 10))) (concat (mux (sgt v_5158 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5158 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5158 2 10))) (concat (mux (sgt v_5168 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5168 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5168 2 10))) (concat (mux (sgt v_5178 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5178 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5178 2 10))) (concat (mux (sgt v_5188 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5188 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5188 2 10))) (concat (mux (sgt v_5198 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5198 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5198 2 10))) (concat (mux (sgt v_5208 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5208 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5208 2 10))) (concat (mux (sgt v_5218 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5218 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5218 2 10))) (concat (mux (sgt v_5228 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5228 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5228 2 10))) (concat (mux (sgt v_5238 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5238 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5238 2 10))) (concat (mux (sgt v_5248 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5248 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5248 2 10))) (concat (mux (sgt v_5258 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5258 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5258 2 10))) (concat (mux (sgt v_5268 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5268 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5268 2 10))) (concat (mux (sgt v_5278 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5278 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5278 2 10))) (mux (sgt v_5288 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5288 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5288 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2598 : reg (bv 256)) (v_2599 : reg (bv 256)) (v_2600 : reg (bv 256)) => do
      v_5315 <- getRegister v_2599;
      v_5318 <- getRegister v_2598;
      v_5321 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 0 8)) (concat (expression.bv_nat 2 0) (extract v_5318 0 8)));
      v_5331 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 8 16)) (concat (expression.bv_nat 2 0) (extract v_5318 8 16)));
      v_5341 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 16 24)) (concat (expression.bv_nat 2 0) (extract v_5318 16 24)));
      v_5351 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 24 32)) (concat (expression.bv_nat 2 0) (extract v_5318 24 32)));
      v_5361 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 32 40)) (concat (expression.bv_nat 2 0) (extract v_5318 32 40)));
      v_5371 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 40 48)) (concat (expression.bv_nat 2 0) (extract v_5318 40 48)));
      v_5381 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 48 56)) (concat (expression.bv_nat 2 0) (extract v_5318 48 56)));
      v_5391 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 56 64)) (concat (expression.bv_nat 2 0) (extract v_5318 56 64)));
      v_5401 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 64 72)) (concat (expression.bv_nat 2 0) (extract v_5318 64 72)));
      v_5411 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 72 80)) (concat (expression.bv_nat 2 0) (extract v_5318 72 80)));
      v_5421 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 80 88)) (concat (expression.bv_nat 2 0) (extract v_5318 80 88)));
      v_5431 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 88 96)) (concat (expression.bv_nat 2 0) (extract v_5318 88 96)));
      v_5441 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 96 104)) (concat (expression.bv_nat 2 0) (extract v_5318 96 104)));
      v_5451 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 104 112)) (concat (expression.bv_nat 2 0) (extract v_5318 104 112)));
      v_5461 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 112 120)) (concat (expression.bv_nat 2 0) (extract v_5318 112 120)));
      v_5471 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 120 128)) (concat (expression.bv_nat 2 0) (extract v_5318 120 128)));
      v_5481 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 128 136)) (concat (expression.bv_nat 2 0) (extract v_5318 128 136)));
      v_5491 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 136 144)) (concat (expression.bv_nat 2 0) (extract v_5318 136 144)));
      v_5501 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 144 152)) (concat (expression.bv_nat 2 0) (extract v_5318 144 152)));
      v_5511 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 152 160)) (concat (expression.bv_nat 2 0) (extract v_5318 152 160)));
      v_5521 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 160 168)) (concat (expression.bv_nat 2 0) (extract v_5318 160 168)));
      v_5531 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 168 176)) (concat (expression.bv_nat 2 0) (extract v_5318 168 176)));
      v_5541 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 176 184)) (concat (expression.bv_nat 2 0) (extract v_5318 176 184)));
      v_5551 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 184 192)) (concat (expression.bv_nat 2 0) (extract v_5318 184 192)));
      v_5561 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 192 200)) (concat (expression.bv_nat 2 0) (extract v_5318 192 200)));
      v_5571 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 200 208)) (concat (expression.bv_nat 2 0) (extract v_5318 200 208)));
      v_5581 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 208 216)) (concat (expression.bv_nat 2 0) (extract v_5318 208 216)));
      v_5591 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 216 224)) (concat (expression.bv_nat 2 0) (extract v_5318 216 224)));
      v_5601 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 224 232)) (concat (expression.bv_nat 2 0) (extract v_5318 224 232)));
      v_5611 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 232 240)) (concat (expression.bv_nat 2 0) (extract v_5318 232 240)));
      v_5621 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 240 248)) (concat (expression.bv_nat 2 0) (extract v_5318 240 248)));
      v_5631 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_5315 248 256)) (concat (expression.bv_nat 2 0) (extract v_5318 248 256)));
      setRegister (lhs.of_reg v_2600) (concat (mux (sgt v_5321 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5321 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5321 2 10))) (concat (mux (sgt v_5331 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5331 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5331 2 10))) (concat (mux (sgt v_5341 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5341 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5341 2 10))) (concat (mux (sgt v_5351 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5351 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5351 2 10))) (concat (mux (sgt v_5361 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5361 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5361 2 10))) (concat (mux (sgt v_5371 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5371 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5371 2 10))) (concat (mux (sgt v_5381 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5381 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5381 2 10))) (concat (mux (sgt v_5391 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5391 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5391 2 10))) (concat (mux (sgt v_5401 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5401 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5401 2 10))) (concat (mux (sgt v_5411 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5411 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5411 2 10))) (concat (mux (sgt v_5421 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5421 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5421 2 10))) (concat (mux (sgt v_5431 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5431 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5431 2 10))) (concat (mux (sgt v_5441 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5441 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5441 2 10))) (concat (mux (sgt v_5451 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5451 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5451 2 10))) (concat (mux (sgt v_5461 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5461 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5461 2 10))) (concat (mux (sgt v_5471 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5471 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5471 2 10))) (concat (mux (sgt v_5481 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5481 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5481 2 10))) (concat (mux (sgt v_5491 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5491 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5491 2 10))) (concat (mux (sgt v_5501 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5501 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5501 2 10))) (concat (mux (sgt v_5511 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5511 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5511 2 10))) (concat (mux (sgt v_5521 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5521 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5521 2 10))) (concat (mux (sgt v_5531 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5531 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5531 2 10))) (concat (mux (sgt v_5541 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5541 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5541 2 10))) (concat (mux (sgt v_5551 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5551 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5551 2 10))) (concat (mux (sgt v_5561 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5561 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5561 2 10))) (concat (mux (sgt v_5571 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5571 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5571 2 10))) (concat (mux (sgt v_5581 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5581 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5581 2 10))) (concat (mux (sgt v_5591 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5591 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5591 2 10))) (concat (mux (sgt v_5601 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5601 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5601 2 10))) (concat (mux (sgt v_5611 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5611 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5611 2 10))) (concat (mux (sgt v_5621 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5621 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5621 2 10))) (mux (sgt v_5631 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_5631 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_5631 2 10))))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2581 : Mem) (v_2582 : reg (bv 128)) (v_2583 : reg (bv 128)) => do
      v_11252 <- getRegister v_2582;
      v_11255 <- evaluateAddress v_2581;
      v_11256 <- load v_11255 16;
      v_11259 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 0 8)) (concat (expression.bv_nat 2 0) (extract v_11256 0 8)));
      v_11269 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 8 16)) (concat (expression.bv_nat 2 0) (extract v_11256 8 16)));
      v_11279 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 16 24)) (concat (expression.bv_nat 2 0) (extract v_11256 16 24)));
      v_11289 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 24 32)) (concat (expression.bv_nat 2 0) (extract v_11256 24 32)));
      v_11299 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 32 40)) (concat (expression.bv_nat 2 0) (extract v_11256 32 40)));
      v_11309 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 40 48)) (concat (expression.bv_nat 2 0) (extract v_11256 40 48)));
      v_11319 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 48 56)) (concat (expression.bv_nat 2 0) (extract v_11256 48 56)));
      v_11329 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 56 64)) (concat (expression.bv_nat 2 0) (extract v_11256 56 64)));
      v_11339 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 64 72)) (concat (expression.bv_nat 2 0) (extract v_11256 64 72)));
      v_11349 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 72 80)) (concat (expression.bv_nat 2 0) (extract v_11256 72 80)));
      v_11359 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 80 88)) (concat (expression.bv_nat 2 0) (extract v_11256 80 88)));
      v_11369 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 88 96)) (concat (expression.bv_nat 2 0) (extract v_11256 88 96)));
      v_11379 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 96 104)) (concat (expression.bv_nat 2 0) (extract v_11256 96 104)));
      v_11389 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 104 112)) (concat (expression.bv_nat 2 0) (extract v_11256 104 112)));
      v_11399 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 112 120)) (concat (expression.bv_nat 2 0) (extract v_11256 112 120)));
      v_11409 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11252 120 128)) (concat (expression.bv_nat 2 0) (extract v_11256 120 128)));
      setRegister (lhs.of_reg v_2583) (concat (mux (sgt v_11259 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11259 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11259 2 10))) (concat (mux (sgt v_11269 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11269 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11269 2 10))) (concat (mux (sgt v_11279 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11279 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11279 2 10))) (concat (mux (sgt v_11289 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11289 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11289 2 10))) (concat (mux (sgt v_11299 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11299 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11299 2 10))) (concat (mux (sgt v_11309 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11309 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11309 2 10))) (concat (mux (sgt v_11319 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11319 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11319 2 10))) (concat (mux (sgt v_11329 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11329 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11329 2 10))) (concat (mux (sgt v_11339 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11339 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11339 2 10))) (concat (mux (sgt v_11349 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11349 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11349 2 10))) (concat (mux (sgt v_11359 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11359 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11359 2 10))) (concat (mux (sgt v_11369 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11369 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11369 2 10))) (concat (mux (sgt v_11379 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11379 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11379 2 10))) (concat (mux (sgt v_11389 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11389 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11389 2 10))) (concat (mux (sgt v_11399 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11399 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11399 2 10))) (mux (sgt v_11409 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11409 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11409 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2593 : reg (bv 256)) (v_2594 : reg (bv 256)) => do
      v_11431 <- getRegister v_2593;
      v_11434 <- evaluateAddress v_2592;
      v_11435 <- load v_11434 32;
      v_11438 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 0 8)) (concat (expression.bv_nat 2 0) (extract v_11435 0 8)));
      v_11448 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 8 16)) (concat (expression.bv_nat 2 0) (extract v_11435 8 16)));
      v_11458 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 16 24)) (concat (expression.bv_nat 2 0) (extract v_11435 16 24)));
      v_11468 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 24 32)) (concat (expression.bv_nat 2 0) (extract v_11435 24 32)));
      v_11478 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 32 40)) (concat (expression.bv_nat 2 0) (extract v_11435 32 40)));
      v_11488 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 40 48)) (concat (expression.bv_nat 2 0) (extract v_11435 40 48)));
      v_11498 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 48 56)) (concat (expression.bv_nat 2 0) (extract v_11435 48 56)));
      v_11508 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 56 64)) (concat (expression.bv_nat 2 0) (extract v_11435 56 64)));
      v_11518 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 64 72)) (concat (expression.bv_nat 2 0) (extract v_11435 64 72)));
      v_11528 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 72 80)) (concat (expression.bv_nat 2 0) (extract v_11435 72 80)));
      v_11538 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 80 88)) (concat (expression.bv_nat 2 0) (extract v_11435 80 88)));
      v_11548 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 88 96)) (concat (expression.bv_nat 2 0) (extract v_11435 88 96)));
      v_11558 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 96 104)) (concat (expression.bv_nat 2 0) (extract v_11435 96 104)));
      v_11568 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 104 112)) (concat (expression.bv_nat 2 0) (extract v_11435 104 112)));
      v_11578 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 112 120)) (concat (expression.bv_nat 2 0) (extract v_11435 112 120)));
      v_11588 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 120 128)) (concat (expression.bv_nat 2 0) (extract v_11435 120 128)));
      v_11598 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 128 136)) (concat (expression.bv_nat 2 0) (extract v_11435 128 136)));
      v_11608 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 136 144)) (concat (expression.bv_nat 2 0) (extract v_11435 136 144)));
      v_11618 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 144 152)) (concat (expression.bv_nat 2 0) (extract v_11435 144 152)));
      v_11628 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 152 160)) (concat (expression.bv_nat 2 0) (extract v_11435 152 160)));
      v_11638 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 160 168)) (concat (expression.bv_nat 2 0) (extract v_11435 160 168)));
      v_11648 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 168 176)) (concat (expression.bv_nat 2 0) (extract v_11435 168 176)));
      v_11658 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 176 184)) (concat (expression.bv_nat 2 0) (extract v_11435 176 184)));
      v_11668 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 184 192)) (concat (expression.bv_nat 2 0) (extract v_11435 184 192)));
      v_11678 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 192 200)) (concat (expression.bv_nat 2 0) (extract v_11435 192 200)));
      v_11688 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 200 208)) (concat (expression.bv_nat 2 0) (extract v_11435 200 208)));
      v_11698 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 208 216)) (concat (expression.bv_nat 2 0) (extract v_11435 208 216)));
      v_11708 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 216 224)) (concat (expression.bv_nat 2 0) (extract v_11435 216 224)));
      v_11718 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 224 232)) (concat (expression.bv_nat 2 0) (extract v_11435 224 232)));
      v_11728 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 232 240)) (concat (expression.bv_nat 2 0) (extract v_11435 232 240)));
      v_11738 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 240 248)) (concat (expression.bv_nat 2 0) (extract v_11435 240 248)));
      v_11748 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_11431 248 256)) (concat (expression.bv_nat 2 0) (extract v_11435 248 256)));
      setRegister (lhs.of_reg v_2594) (concat (mux (sgt v_11438 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11438 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11438 2 10))) (concat (mux (sgt v_11448 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11448 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11448 2 10))) (concat (mux (sgt v_11458 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11458 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11458 2 10))) (concat (mux (sgt v_11468 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11468 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11468 2 10))) (concat (mux (sgt v_11478 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11478 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11478 2 10))) (concat (mux (sgt v_11488 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11488 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11488 2 10))) (concat (mux (sgt v_11498 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11498 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11498 2 10))) (concat (mux (sgt v_11508 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11508 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11508 2 10))) (concat (mux (sgt v_11518 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11518 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11518 2 10))) (concat (mux (sgt v_11528 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11528 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11528 2 10))) (concat (mux (sgt v_11538 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11538 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11538 2 10))) (concat (mux (sgt v_11548 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11548 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11548 2 10))) (concat (mux (sgt v_11558 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11558 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11558 2 10))) (concat (mux (sgt v_11568 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11568 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11568 2 10))) (concat (mux (sgt v_11578 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11578 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11578 2 10))) (concat (mux (sgt v_11588 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11588 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11588 2 10))) (concat (mux (sgt v_11598 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11598 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11598 2 10))) (concat (mux (sgt v_11608 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11608 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11608 2 10))) (concat (mux (sgt v_11618 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11618 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11618 2 10))) (concat (mux (sgt v_11628 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11628 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11628 2 10))) (concat (mux (sgt v_11638 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11638 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11638 2 10))) (concat (mux (sgt v_11648 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11648 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11648 2 10))) (concat (mux (sgt v_11658 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11658 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11658 2 10))) (concat (mux (sgt v_11668 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11668 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11668 2 10))) (concat (mux (sgt v_11678 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11678 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11678 2 10))) (concat (mux (sgt v_11688 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11688 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11688 2 10))) (concat (mux (sgt v_11698 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11698 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11698 2 10))) (concat (mux (sgt v_11708 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11708 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11708 2 10))) (concat (mux (sgt v_11718 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11718 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11718 2 10))) (concat (mux (sgt v_11728 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11728 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11728 2 10))) (concat (mux (sgt v_11738 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11738 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11738 2 10))) (mux (sgt v_11748 (expression.bv_nat 10 255)) (expression.bv_nat 8 255) (mux (slt v_11748 (expression.bv_nat 10 0)) (expression.bv_nat 8 0) (extract v_11748 2 10))))))))))))))))))))))))))))))))));
      pure ()
    pat_end
