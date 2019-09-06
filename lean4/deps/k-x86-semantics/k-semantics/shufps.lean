def shufps1 : instruction :=
  definst "shufps" $ do
    pattern fun (v_3138 : imm int) (v_3139 : reg (bv 128)) (v_3140 : reg (bv 128)) => do
      v_5435 <- eval (handleImmediateWithSignExtend v_3138 8 8);
      v_5437 <- eval (isBitSet v_5435 0);
      v_5438 <- getRegister v_3139;
      v_5439 <- eval (extract v_5438 0 32);
      v_5440 <- eval (extract v_5438 64 96);
      v_5442 <- eval (extract v_5438 32 64);
      v_5443 <- eval (extract v_5438 96 128);
      v_5447 <- eval (isBitSet v_5435 2);
      v_5452 <- eval (isBitSet v_5435 4);
      v_5453 <- getRegister v_3140;
      v_5454 <- eval (extract v_5453 0 32);
      v_5455 <- eval (extract v_5453 64 96);
      v_5457 <- eval (extract v_5453 32 64);
      v_5458 <- eval (extract v_5453 96 128);
      v_5462 <- eval (isBitSet v_5435 6);
      setRegister (lhs.of_reg v_3140) (concat (mux (isBitSet v_5435 1) (mux v_5437 v_5439 v_5440) (mux v_5437 v_5442 v_5443)) (concat (mux (isBitSet v_5435 3) (mux v_5447 v_5439 v_5440) (mux v_5447 v_5442 v_5443)) (concat (mux (isBitSet v_5435 5) (mux v_5452 v_5454 v_5455) (mux v_5452 v_5457 v_5458)) (mux (isBitSet v_5435 7) (mux v_5462 v_5454 v_5455) (mux v_5462 v_5457 v_5458)))));
      pure ()
    pat_end;
    pattern fun (v_3134 : imm int) (v_3133 : Mem) (v_3135 : reg (bv 128)) => do
      v_8501 <- eval (handleImmediateWithSignExtend v_3134 8 8);
      v_8503 <- eval (isBitSet v_8501 0);
      v_8504 <- evaluateAddress v_3133;
      v_8505 <- load v_8504 16;
      v_8506 <- eval (extract v_8505 0 32);
      v_8507 <- eval (extract v_8505 64 96);
      v_8509 <- eval (extract v_8505 32 64);
      v_8510 <- eval (extract v_8505 96 128);
      v_8514 <- eval (isBitSet v_8501 2);
      v_8519 <- eval (isBitSet v_8501 4);
      v_8520 <- getRegister v_3135;
      v_8521 <- eval (extract v_8520 0 32);
      v_8522 <- eval (extract v_8520 64 96);
      v_8524 <- eval (extract v_8520 32 64);
      v_8525 <- eval (extract v_8520 96 128);
      v_8529 <- eval (isBitSet v_8501 6);
      setRegister (lhs.of_reg v_3135) (concat (mux (isBitSet v_8501 1) (mux v_8503 v_8506 v_8507) (mux v_8503 v_8509 v_8510)) (concat (mux (isBitSet v_8501 3) (mux v_8514 v_8506 v_8507) (mux v_8514 v_8509 v_8510)) (concat (mux (isBitSet v_8501 5) (mux v_8519 v_8521 v_8522) (mux v_8519 v_8524 v_8525)) (mux (isBitSet v_8501 7) (mux v_8529 v_8521 v_8522) (mux v_8529 v_8524 v_8525)))));
      pure ()
    pat_end
