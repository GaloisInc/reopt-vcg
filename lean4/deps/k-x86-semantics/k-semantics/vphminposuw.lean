def vphminposuw1 : instruction :=
  definst "vphminposuw" $ do
    pattern fun (v_3279 : reg (bv 128)) (v_3280 : reg (bv 128)) => do
      v_9112 <- getRegister v_3279;
      v_9113 <- eval (extract v_9112 0 16);
      v_9114 <- eval (extract v_9112 16 32);
      v_9115 <- eval (extract v_9112 32 48);
      v_9116 <- eval (extract v_9112 48 64);
      v_9117 <- eval (extract v_9112 64 80);
      v_9118 <- eval (extract v_9112 80 96);
      v_9119 <- eval (extract v_9112 96 112);
      v_9120 <- eval (extract v_9112 112 128);
      v_9121 <- eval (ult v_9119 v_9120);
      v_9122 <- eval (mux v_9121 v_9119 v_9120);
      v_9123 <- eval (ult v_9118 v_9122);
      v_9124 <- eval (mux v_9123 v_9118 v_9122);
      v_9125 <- eval (ult v_9117 v_9124);
      v_9126 <- eval (mux v_9125 v_9117 v_9124);
      v_9127 <- eval (ult v_9116 v_9126);
      v_9128 <- eval (mux v_9127 v_9116 v_9126);
      v_9129 <- eval (ult v_9115 v_9128);
      v_9130 <- eval (mux v_9129 v_9115 v_9128);
      v_9131 <- eval (ult v_9114 v_9130);
      v_9132 <- eval (mux v_9131 v_9114 v_9130);
      v_9133 <- eval (ult v_9113 v_9132);
      setRegister (lhs.of_reg v_3280) (concat (mux v_9133 (expression.bv_nat 112 7) (mux v_9131 (expression.bv_nat 112 6) (mux v_9129 (expression.bv_nat 112 5) (mux v_9127 (expression.bv_nat 112 4) (mux v_9125 (expression.bv_nat 112 3) (mux v_9123 (expression.bv_nat 112 2) (mux v_9121 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_9133 v_9113 v_9132));
      pure ()
    pat_end;
    pattern fun (v_3274 : Mem) (v_3275 : reg (bv 128)) => do
      v_17509 <- evaluateAddress v_3274;
      v_17510 <- load v_17509 16;
      v_17511 <- eval (extract v_17510 0 16);
      v_17512 <- eval (extract v_17510 16 32);
      v_17513 <- eval (extract v_17510 32 48);
      v_17514 <- eval (extract v_17510 48 64);
      v_17515 <- eval (extract v_17510 64 80);
      v_17516 <- eval (extract v_17510 80 96);
      v_17517 <- eval (extract v_17510 96 112);
      v_17518 <- eval (extract v_17510 112 128);
      v_17519 <- eval (ult v_17517 v_17518);
      v_17520 <- eval (mux v_17519 v_17517 v_17518);
      v_17521 <- eval (ult v_17516 v_17520);
      v_17522 <- eval (mux v_17521 v_17516 v_17520);
      v_17523 <- eval (ult v_17515 v_17522);
      v_17524 <- eval (mux v_17523 v_17515 v_17522);
      v_17525 <- eval (ult v_17514 v_17524);
      v_17526 <- eval (mux v_17525 v_17514 v_17524);
      v_17527 <- eval (ult v_17513 v_17526);
      v_17528 <- eval (mux v_17527 v_17513 v_17526);
      v_17529 <- eval (ult v_17512 v_17528);
      v_17530 <- eval (mux v_17529 v_17512 v_17528);
      v_17531 <- eval (ult v_17511 v_17530);
      setRegister (lhs.of_reg v_3275) (concat (mux v_17531 (expression.bv_nat 112 7) (mux v_17529 (expression.bv_nat 112 6) (mux v_17527 (expression.bv_nat 112 5) (mux v_17525 (expression.bv_nat 112 4) (mux v_17523 (expression.bv_nat 112 3) (mux v_17521 (expression.bv_nat 112 2) (mux v_17519 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_17531 v_17511 v_17530));
      pure ()
    pat_end
