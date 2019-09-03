def vpsubsb1 : instruction :=
  definst "vpsubsb" $ do
    pattern fun (v_2452 : reg (bv 128)) (v_2453 : reg (bv 128)) (v_2454 : reg (bv 128)) => do
      v_4221 <- getRegister v_2453;
      v_4225 <- getRegister v_2452;
      v_4229 <- eval (sub (mi 10 (svalueMInt (extract v_4221 0 8))) (mi 10 (svalueMInt (extract v_4225 0 8))));
      v_4241 <- eval (sub (mi 10 (svalueMInt (extract v_4221 8 16))) (mi 10 (svalueMInt (extract v_4225 8 16))));
      v_4253 <- eval (sub (mi 10 (svalueMInt (extract v_4221 16 24))) (mi 10 (svalueMInt (extract v_4225 16 24))));
      v_4265 <- eval (sub (mi 10 (svalueMInt (extract v_4221 24 32))) (mi 10 (svalueMInt (extract v_4225 24 32))));
      v_4277 <- eval (sub (mi 10 (svalueMInt (extract v_4221 32 40))) (mi 10 (svalueMInt (extract v_4225 32 40))));
      v_4289 <- eval (sub (mi 10 (svalueMInt (extract v_4221 40 48))) (mi 10 (svalueMInt (extract v_4225 40 48))));
      v_4301 <- eval (sub (mi 10 (svalueMInt (extract v_4221 48 56))) (mi 10 (svalueMInt (extract v_4225 48 56))));
      v_4313 <- eval (sub (mi 10 (svalueMInt (extract v_4221 56 64))) (mi 10 (svalueMInt (extract v_4225 56 64))));
      v_4325 <- eval (sub (mi 10 (svalueMInt (extract v_4221 64 72))) (mi 10 (svalueMInt (extract v_4225 64 72))));
      v_4337 <- eval (sub (mi 10 (svalueMInt (extract v_4221 72 80))) (mi 10 (svalueMInt (extract v_4225 72 80))));
      v_4349 <- eval (sub (mi 10 (svalueMInt (extract v_4221 80 88))) (mi 10 (svalueMInt (extract v_4225 80 88))));
      v_4361 <- eval (sub (mi 10 (svalueMInt (extract v_4221 88 96))) (mi 10 (svalueMInt (extract v_4225 88 96))));
      v_4373 <- eval (sub (mi 10 (svalueMInt (extract v_4221 96 104))) (mi 10 (svalueMInt (extract v_4225 96 104))));
      v_4385 <- eval (sub (mi 10 (svalueMInt (extract v_4221 104 112))) (mi 10 (svalueMInt (extract v_4225 104 112))));
      v_4397 <- eval (sub (mi 10 (svalueMInt (extract v_4221 112 120))) (mi 10 (svalueMInt (extract v_4225 112 120))));
      v_4409 <- eval (sub (mi 10 (svalueMInt (extract v_4221 120 128))) (mi 10 (svalueMInt (extract v_4225 120 128))));
      setRegister (lhs.of_reg v_2454) (concat (mux (sgt v_4229 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4229 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4229 2 10))) (concat (mux (sgt v_4241 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4241 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4241 2 10))) (concat (mux (sgt v_4253 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4253 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4253 2 10))) (concat (mux (sgt v_4265 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4265 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4265 2 10))) (concat (mux (sgt v_4277 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4277 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4277 2 10))) (concat (mux (sgt v_4289 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4289 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4289 2 10))) (concat (mux (sgt v_4301 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4301 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4301 2 10))) (concat (mux (sgt v_4313 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4313 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4313 2 10))) (concat (mux (sgt v_4325 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4325 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4325 2 10))) (concat (mux (sgt v_4337 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4337 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4337 2 10))) (concat (mux (sgt v_4349 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4349 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4349 2 10))) (concat (mux (sgt v_4361 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4361 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4361 2 10))) (concat (mux (sgt v_4373 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4373 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4373 2 10))) (concat (mux (sgt v_4385 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4385 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4385 2 10))) (concat (mux (sgt v_4397 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4397 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4397 2 10))) (mux (sgt v_4409 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4409 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4409 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2462 : reg (bv 256)) (v_2463 : reg (bv 256)) (v_2464 : reg (bv 256)) => do
      v_4436 <- getRegister v_2463;
      v_4440 <- getRegister v_2462;
      v_4444 <- eval (sub (mi 10 (svalueMInt (extract v_4436 0 8))) (mi 10 (svalueMInt (extract v_4440 0 8))));
      v_4456 <- eval (sub (mi 10 (svalueMInt (extract v_4436 8 16))) (mi 10 (svalueMInt (extract v_4440 8 16))));
      v_4468 <- eval (sub (mi 10 (svalueMInt (extract v_4436 16 24))) (mi 10 (svalueMInt (extract v_4440 16 24))));
      v_4480 <- eval (sub (mi 10 (svalueMInt (extract v_4436 24 32))) (mi 10 (svalueMInt (extract v_4440 24 32))));
      v_4492 <- eval (sub (mi 10 (svalueMInt (extract v_4436 32 40))) (mi 10 (svalueMInt (extract v_4440 32 40))));
      v_4504 <- eval (sub (mi 10 (svalueMInt (extract v_4436 40 48))) (mi 10 (svalueMInt (extract v_4440 40 48))));
      v_4516 <- eval (sub (mi 10 (svalueMInt (extract v_4436 48 56))) (mi 10 (svalueMInt (extract v_4440 48 56))));
      v_4528 <- eval (sub (mi 10 (svalueMInt (extract v_4436 56 64))) (mi 10 (svalueMInt (extract v_4440 56 64))));
      v_4540 <- eval (sub (mi 10 (svalueMInt (extract v_4436 64 72))) (mi 10 (svalueMInt (extract v_4440 64 72))));
      v_4552 <- eval (sub (mi 10 (svalueMInt (extract v_4436 72 80))) (mi 10 (svalueMInt (extract v_4440 72 80))));
      v_4564 <- eval (sub (mi 10 (svalueMInt (extract v_4436 80 88))) (mi 10 (svalueMInt (extract v_4440 80 88))));
      v_4576 <- eval (sub (mi 10 (svalueMInt (extract v_4436 88 96))) (mi 10 (svalueMInt (extract v_4440 88 96))));
      v_4588 <- eval (sub (mi 10 (svalueMInt (extract v_4436 96 104))) (mi 10 (svalueMInt (extract v_4440 96 104))));
      v_4600 <- eval (sub (mi 10 (svalueMInt (extract v_4436 104 112))) (mi 10 (svalueMInt (extract v_4440 104 112))));
      v_4612 <- eval (sub (mi 10 (svalueMInt (extract v_4436 112 120))) (mi 10 (svalueMInt (extract v_4440 112 120))));
      v_4624 <- eval (sub (mi 10 (svalueMInt (extract v_4436 120 128))) (mi 10 (svalueMInt (extract v_4440 120 128))));
      v_4636 <- eval (sub (mi 10 (svalueMInt (extract v_4436 128 136))) (mi 10 (svalueMInt (extract v_4440 128 136))));
      v_4648 <- eval (sub (mi 10 (svalueMInt (extract v_4436 136 144))) (mi 10 (svalueMInt (extract v_4440 136 144))));
      v_4660 <- eval (sub (mi 10 (svalueMInt (extract v_4436 144 152))) (mi 10 (svalueMInt (extract v_4440 144 152))));
      v_4672 <- eval (sub (mi 10 (svalueMInt (extract v_4436 152 160))) (mi 10 (svalueMInt (extract v_4440 152 160))));
      v_4684 <- eval (sub (mi 10 (svalueMInt (extract v_4436 160 168))) (mi 10 (svalueMInt (extract v_4440 160 168))));
      v_4696 <- eval (sub (mi 10 (svalueMInt (extract v_4436 168 176))) (mi 10 (svalueMInt (extract v_4440 168 176))));
      v_4708 <- eval (sub (mi 10 (svalueMInt (extract v_4436 176 184))) (mi 10 (svalueMInt (extract v_4440 176 184))));
      v_4720 <- eval (sub (mi 10 (svalueMInt (extract v_4436 184 192))) (mi 10 (svalueMInt (extract v_4440 184 192))));
      v_4732 <- eval (sub (mi 10 (svalueMInt (extract v_4436 192 200))) (mi 10 (svalueMInt (extract v_4440 192 200))));
      v_4744 <- eval (sub (mi 10 (svalueMInt (extract v_4436 200 208))) (mi 10 (svalueMInt (extract v_4440 200 208))));
      v_4756 <- eval (sub (mi 10 (svalueMInt (extract v_4436 208 216))) (mi 10 (svalueMInt (extract v_4440 208 216))));
      v_4768 <- eval (sub (mi 10 (svalueMInt (extract v_4436 216 224))) (mi 10 (svalueMInt (extract v_4440 216 224))));
      v_4780 <- eval (sub (mi 10 (svalueMInt (extract v_4436 224 232))) (mi 10 (svalueMInt (extract v_4440 224 232))));
      v_4792 <- eval (sub (mi 10 (svalueMInt (extract v_4436 232 240))) (mi 10 (svalueMInt (extract v_4440 232 240))));
      v_4804 <- eval (sub (mi 10 (svalueMInt (extract v_4436 240 248))) (mi 10 (svalueMInt (extract v_4440 240 248))));
      v_4816 <- eval (sub (mi 10 (svalueMInt (extract v_4436 248 256))) (mi 10 (svalueMInt (extract v_4440 248 256))));
      setRegister (lhs.of_reg v_2464) (concat (mux (sgt v_4444 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4444 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4444 2 10))) (concat (mux (sgt v_4456 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4456 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4456 2 10))) (concat (mux (sgt v_4468 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4468 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4468 2 10))) (concat (mux (sgt v_4480 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4480 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4480 2 10))) (concat (mux (sgt v_4492 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4492 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4492 2 10))) (concat (mux (sgt v_4504 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4504 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4504 2 10))) (concat (mux (sgt v_4516 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4516 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4516 2 10))) (concat (mux (sgt v_4528 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4528 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4528 2 10))) (concat (mux (sgt v_4540 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4540 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4540 2 10))) (concat (mux (sgt v_4552 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4552 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4552 2 10))) (concat (mux (sgt v_4564 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4564 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4564 2 10))) (concat (mux (sgt v_4576 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4576 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4576 2 10))) (concat (mux (sgt v_4588 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4588 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4588 2 10))) (concat (mux (sgt v_4600 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4600 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4600 2 10))) (concat (mux (sgt v_4612 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4612 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4612 2 10))) (concat (mux (sgt v_4624 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4624 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4624 2 10))) (concat (mux (sgt v_4636 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4636 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4636 2 10))) (concat (mux (sgt v_4648 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4648 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4648 2 10))) (concat (mux (sgt v_4660 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4660 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4660 2 10))) (concat (mux (sgt v_4672 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4672 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4672 2 10))) (concat (mux (sgt v_4684 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4684 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4684 2 10))) (concat (mux (sgt v_4696 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4696 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4696 2 10))) (concat (mux (sgt v_4708 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4708 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4708 2 10))) (concat (mux (sgt v_4720 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4720 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4720 2 10))) (concat (mux (sgt v_4732 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4732 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4732 2 10))) (concat (mux (sgt v_4744 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4744 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4744 2 10))) (concat (mux (sgt v_4756 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4756 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4756 2 10))) (concat (mux (sgt v_4768 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4768 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4768 2 10))) (concat (mux (sgt v_4780 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4780 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4780 2 10))) (concat (mux (sgt v_4792 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4792 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4792 2 10))) (concat (mux (sgt v_4804 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4804 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4804 2 10))) (mux (sgt v_4816 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4816 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4816 2 10))))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2446 : Mem) (v_2447 : reg (bv 128)) (v_2448 : reg (bv 128)) => do
      v_10598 <- getRegister v_2447;
      v_10602 <- evaluateAddress v_2446;
      v_10603 <- load v_10602 16;
      v_10607 <- eval (sub (mi 10 (svalueMInt (extract v_10598 0 8))) (mi 10 (svalueMInt (extract v_10603 0 8))));
      v_10619 <- eval (sub (mi 10 (svalueMInt (extract v_10598 8 16))) (mi 10 (svalueMInt (extract v_10603 8 16))));
      v_10631 <- eval (sub (mi 10 (svalueMInt (extract v_10598 16 24))) (mi 10 (svalueMInt (extract v_10603 16 24))));
      v_10643 <- eval (sub (mi 10 (svalueMInt (extract v_10598 24 32))) (mi 10 (svalueMInt (extract v_10603 24 32))));
      v_10655 <- eval (sub (mi 10 (svalueMInt (extract v_10598 32 40))) (mi 10 (svalueMInt (extract v_10603 32 40))));
      v_10667 <- eval (sub (mi 10 (svalueMInt (extract v_10598 40 48))) (mi 10 (svalueMInt (extract v_10603 40 48))));
      v_10679 <- eval (sub (mi 10 (svalueMInt (extract v_10598 48 56))) (mi 10 (svalueMInt (extract v_10603 48 56))));
      v_10691 <- eval (sub (mi 10 (svalueMInt (extract v_10598 56 64))) (mi 10 (svalueMInt (extract v_10603 56 64))));
      v_10703 <- eval (sub (mi 10 (svalueMInt (extract v_10598 64 72))) (mi 10 (svalueMInt (extract v_10603 64 72))));
      v_10715 <- eval (sub (mi 10 (svalueMInt (extract v_10598 72 80))) (mi 10 (svalueMInt (extract v_10603 72 80))));
      v_10727 <- eval (sub (mi 10 (svalueMInt (extract v_10598 80 88))) (mi 10 (svalueMInt (extract v_10603 80 88))));
      v_10739 <- eval (sub (mi 10 (svalueMInt (extract v_10598 88 96))) (mi 10 (svalueMInt (extract v_10603 88 96))));
      v_10751 <- eval (sub (mi 10 (svalueMInt (extract v_10598 96 104))) (mi 10 (svalueMInt (extract v_10603 96 104))));
      v_10763 <- eval (sub (mi 10 (svalueMInt (extract v_10598 104 112))) (mi 10 (svalueMInt (extract v_10603 104 112))));
      v_10775 <- eval (sub (mi 10 (svalueMInt (extract v_10598 112 120))) (mi 10 (svalueMInt (extract v_10603 112 120))));
      v_10787 <- eval (sub (mi 10 (svalueMInt (extract v_10598 120 128))) (mi 10 (svalueMInt (extract v_10603 120 128))));
      setRegister (lhs.of_reg v_2448) (concat (mux (sgt v_10607 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10607 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10607 2 10))) (concat (mux (sgt v_10619 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10619 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10619 2 10))) (concat (mux (sgt v_10631 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10631 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10631 2 10))) (concat (mux (sgt v_10643 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10643 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10643 2 10))) (concat (mux (sgt v_10655 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10655 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10655 2 10))) (concat (mux (sgt v_10667 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10667 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10667 2 10))) (concat (mux (sgt v_10679 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10679 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10679 2 10))) (concat (mux (sgt v_10691 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10691 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10691 2 10))) (concat (mux (sgt v_10703 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10703 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10703 2 10))) (concat (mux (sgt v_10715 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10715 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10715 2 10))) (concat (mux (sgt v_10727 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10727 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10727 2 10))) (concat (mux (sgt v_10739 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10739 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10739 2 10))) (concat (mux (sgt v_10751 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10751 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10751 2 10))) (concat (mux (sgt v_10763 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10763 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10763 2 10))) (concat (mux (sgt v_10775 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10775 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10775 2 10))) (mux (sgt v_10787 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10787 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10787 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2457 : Mem) (v_2458 : reg (bv 256)) (v_2459 : reg (bv 256)) => do
      v_10809 <- getRegister v_2458;
      v_10813 <- evaluateAddress v_2457;
      v_10814 <- load v_10813 32;
      v_10818 <- eval (sub (mi 10 (svalueMInt (extract v_10809 0 8))) (mi 10 (svalueMInt (extract v_10814 0 8))));
      v_10830 <- eval (sub (mi 10 (svalueMInt (extract v_10809 8 16))) (mi 10 (svalueMInt (extract v_10814 8 16))));
      v_10842 <- eval (sub (mi 10 (svalueMInt (extract v_10809 16 24))) (mi 10 (svalueMInt (extract v_10814 16 24))));
      v_10854 <- eval (sub (mi 10 (svalueMInt (extract v_10809 24 32))) (mi 10 (svalueMInt (extract v_10814 24 32))));
      v_10866 <- eval (sub (mi 10 (svalueMInt (extract v_10809 32 40))) (mi 10 (svalueMInt (extract v_10814 32 40))));
      v_10878 <- eval (sub (mi 10 (svalueMInt (extract v_10809 40 48))) (mi 10 (svalueMInt (extract v_10814 40 48))));
      v_10890 <- eval (sub (mi 10 (svalueMInt (extract v_10809 48 56))) (mi 10 (svalueMInt (extract v_10814 48 56))));
      v_10902 <- eval (sub (mi 10 (svalueMInt (extract v_10809 56 64))) (mi 10 (svalueMInt (extract v_10814 56 64))));
      v_10914 <- eval (sub (mi 10 (svalueMInt (extract v_10809 64 72))) (mi 10 (svalueMInt (extract v_10814 64 72))));
      v_10926 <- eval (sub (mi 10 (svalueMInt (extract v_10809 72 80))) (mi 10 (svalueMInt (extract v_10814 72 80))));
      v_10938 <- eval (sub (mi 10 (svalueMInt (extract v_10809 80 88))) (mi 10 (svalueMInt (extract v_10814 80 88))));
      v_10950 <- eval (sub (mi 10 (svalueMInt (extract v_10809 88 96))) (mi 10 (svalueMInt (extract v_10814 88 96))));
      v_10962 <- eval (sub (mi 10 (svalueMInt (extract v_10809 96 104))) (mi 10 (svalueMInt (extract v_10814 96 104))));
      v_10974 <- eval (sub (mi 10 (svalueMInt (extract v_10809 104 112))) (mi 10 (svalueMInt (extract v_10814 104 112))));
      v_10986 <- eval (sub (mi 10 (svalueMInt (extract v_10809 112 120))) (mi 10 (svalueMInt (extract v_10814 112 120))));
      v_10998 <- eval (sub (mi 10 (svalueMInt (extract v_10809 120 128))) (mi 10 (svalueMInt (extract v_10814 120 128))));
      v_11010 <- eval (sub (mi 10 (svalueMInt (extract v_10809 128 136))) (mi 10 (svalueMInt (extract v_10814 128 136))));
      v_11022 <- eval (sub (mi 10 (svalueMInt (extract v_10809 136 144))) (mi 10 (svalueMInt (extract v_10814 136 144))));
      v_11034 <- eval (sub (mi 10 (svalueMInt (extract v_10809 144 152))) (mi 10 (svalueMInt (extract v_10814 144 152))));
      v_11046 <- eval (sub (mi 10 (svalueMInt (extract v_10809 152 160))) (mi 10 (svalueMInt (extract v_10814 152 160))));
      v_11058 <- eval (sub (mi 10 (svalueMInt (extract v_10809 160 168))) (mi 10 (svalueMInt (extract v_10814 160 168))));
      v_11070 <- eval (sub (mi 10 (svalueMInt (extract v_10809 168 176))) (mi 10 (svalueMInt (extract v_10814 168 176))));
      v_11082 <- eval (sub (mi 10 (svalueMInt (extract v_10809 176 184))) (mi 10 (svalueMInt (extract v_10814 176 184))));
      v_11094 <- eval (sub (mi 10 (svalueMInt (extract v_10809 184 192))) (mi 10 (svalueMInt (extract v_10814 184 192))));
      v_11106 <- eval (sub (mi 10 (svalueMInt (extract v_10809 192 200))) (mi 10 (svalueMInt (extract v_10814 192 200))));
      v_11118 <- eval (sub (mi 10 (svalueMInt (extract v_10809 200 208))) (mi 10 (svalueMInt (extract v_10814 200 208))));
      v_11130 <- eval (sub (mi 10 (svalueMInt (extract v_10809 208 216))) (mi 10 (svalueMInt (extract v_10814 208 216))));
      v_11142 <- eval (sub (mi 10 (svalueMInt (extract v_10809 216 224))) (mi 10 (svalueMInt (extract v_10814 216 224))));
      v_11154 <- eval (sub (mi 10 (svalueMInt (extract v_10809 224 232))) (mi 10 (svalueMInt (extract v_10814 224 232))));
      v_11166 <- eval (sub (mi 10 (svalueMInt (extract v_10809 232 240))) (mi 10 (svalueMInt (extract v_10814 232 240))));
      v_11178 <- eval (sub (mi 10 (svalueMInt (extract v_10809 240 248))) (mi 10 (svalueMInt (extract v_10814 240 248))));
      v_11190 <- eval (sub (mi 10 (svalueMInt (extract v_10809 248 256))) (mi 10 (svalueMInt (extract v_10814 248 256))));
      setRegister (lhs.of_reg v_2459) (concat (mux (sgt v_10818 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10818 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10818 2 10))) (concat (mux (sgt v_10830 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10830 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10830 2 10))) (concat (mux (sgt v_10842 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10842 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10842 2 10))) (concat (mux (sgt v_10854 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10854 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10854 2 10))) (concat (mux (sgt v_10866 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10866 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10866 2 10))) (concat (mux (sgt v_10878 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10878 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10878 2 10))) (concat (mux (sgt v_10890 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10890 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10890 2 10))) (concat (mux (sgt v_10902 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10902 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10902 2 10))) (concat (mux (sgt v_10914 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10914 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10914 2 10))) (concat (mux (sgt v_10926 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10926 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10926 2 10))) (concat (mux (sgt v_10938 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10938 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10938 2 10))) (concat (mux (sgt v_10950 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10950 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10950 2 10))) (concat (mux (sgt v_10962 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10962 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10962 2 10))) (concat (mux (sgt v_10974 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10974 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10974 2 10))) (concat (mux (sgt v_10986 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10986 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10986 2 10))) (concat (mux (sgt v_10998 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10998 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10998 2 10))) (concat (mux (sgt v_11010 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11010 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11010 2 10))) (concat (mux (sgt v_11022 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11022 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11022 2 10))) (concat (mux (sgt v_11034 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11034 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11034 2 10))) (concat (mux (sgt v_11046 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11046 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11046 2 10))) (concat (mux (sgt v_11058 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11058 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11058 2 10))) (concat (mux (sgt v_11070 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11070 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11070 2 10))) (concat (mux (sgt v_11082 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11082 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11082 2 10))) (concat (mux (sgt v_11094 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11094 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11094 2 10))) (concat (mux (sgt v_11106 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11106 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11106 2 10))) (concat (mux (sgt v_11118 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11118 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11118 2 10))) (concat (mux (sgt v_11130 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11130 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11130 2 10))) (concat (mux (sgt v_11142 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11142 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11142 2 10))) (concat (mux (sgt v_11154 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11154 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11154 2 10))) (concat (mux (sgt v_11166 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11166 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11166 2 10))) (concat (mux (sgt v_11178 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11178 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11178 2 10))) (mux (sgt v_11190 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11190 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11190 2 10))))))))))))))))))))))))))))))))));
      pure ()
    pat_end
