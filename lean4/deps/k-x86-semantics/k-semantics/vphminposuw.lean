def vphminposuw1 : instruction :=
  definst "vphminposuw" $ do
    pattern fun (v_3305 : reg (bv 128)) (v_3306 : reg (bv 128)) => do
      v_9139 <- getRegister v_3305;
      v_9140 <- eval (extract v_9139 0 16);
      v_9141 <- eval (extract v_9139 16 32);
      v_9142 <- eval (extract v_9139 32 48);
      v_9143 <- eval (extract v_9139 48 64);
      v_9144 <- eval (extract v_9139 64 80);
      v_9145 <- eval (extract v_9139 80 96);
      v_9146 <- eval (extract v_9139 96 112);
      v_9147 <- eval (extract v_9139 112 128);
      v_9148 <- eval (ult v_9146 v_9147);
      v_9149 <- eval (mux v_9148 v_9146 v_9147);
      v_9150 <- eval (ult v_9145 v_9149);
      v_9151 <- eval (mux v_9150 v_9145 v_9149);
      v_9152 <- eval (ult v_9144 v_9151);
      v_9153 <- eval (mux v_9152 v_9144 v_9151);
      v_9154 <- eval (ult v_9143 v_9153);
      v_9155 <- eval (mux v_9154 v_9143 v_9153);
      v_9156 <- eval (ult v_9142 v_9155);
      v_9157 <- eval (mux v_9156 v_9142 v_9155);
      v_9158 <- eval (ult v_9141 v_9157);
      v_9159 <- eval (mux v_9158 v_9141 v_9157);
      v_9160 <- eval (ult v_9140 v_9159);
      setRegister (lhs.of_reg v_3306) (concat (mux v_9160 (expression.bv_nat 112 7) (mux v_9158 (expression.bv_nat 112 6) (mux v_9156 (expression.bv_nat 112 5) (mux v_9154 (expression.bv_nat 112 4) (mux v_9152 (expression.bv_nat 112 3) (mux v_9150 (expression.bv_nat 112 2) (mux v_9148 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_9160 v_9140 v_9159));
      pure ()
    pat_end;
    pattern fun (v_3301 : Mem) (v_3302 : reg (bv 128)) => do
      v_17536 <- evaluateAddress v_3301;
      v_17537 <- load v_17536 16;
      v_17538 <- eval (extract v_17537 0 16);
      v_17539 <- eval (extract v_17537 16 32);
      v_17540 <- eval (extract v_17537 32 48);
      v_17541 <- eval (extract v_17537 48 64);
      v_17542 <- eval (extract v_17537 64 80);
      v_17543 <- eval (extract v_17537 80 96);
      v_17544 <- eval (extract v_17537 96 112);
      v_17545 <- eval (extract v_17537 112 128);
      v_17546 <- eval (ult v_17544 v_17545);
      v_17547 <- eval (mux v_17546 v_17544 v_17545);
      v_17548 <- eval (ult v_17543 v_17547);
      v_17549 <- eval (mux v_17548 v_17543 v_17547);
      v_17550 <- eval (ult v_17542 v_17549);
      v_17551 <- eval (mux v_17550 v_17542 v_17549);
      v_17552 <- eval (ult v_17541 v_17551);
      v_17553 <- eval (mux v_17552 v_17541 v_17551);
      v_17554 <- eval (ult v_17540 v_17553);
      v_17555 <- eval (mux v_17554 v_17540 v_17553);
      v_17556 <- eval (ult v_17539 v_17555);
      v_17557 <- eval (mux v_17556 v_17539 v_17555);
      v_17558 <- eval (ult v_17538 v_17557);
      setRegister (lhs.of_reg v_3302) (concat (mux v_17558 (expression.bv_nat 112 7) (mux v_17556 (expression.bv_nat 112 6) (mux v_17554 (expression.bv_nat 112 5) (mux v_17552 (expression.bv_nat 112 4) (mux v_17550 (expression.bv_nat 112 3) (mux v_17548 (expression.bv_nat 112 2) (mux v_17546 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_17558 v_17538 v_17557));
      pure ()
    pat_end
