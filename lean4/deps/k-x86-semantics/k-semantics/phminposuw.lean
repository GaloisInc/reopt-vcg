def phminposuw1 : instruction :=
  definst "phminposuw" $ do
    pattern fun (v_2455 : reg (bv 128)) (v_2456 : reg (bv 128)) => do
      v_4199 <- getRegister v_2455;
      v_4200 <- eval (extract v_4199 0 16);
      v_4201 <- eval (extract v_4199 16 32);
      v_4202 <- eval (extract v_4199 32 48);
      v_4203 <- eval (extract v_4199 48 64);
      v_4204 <- eval (extract v_4199 64 80);
      v_4205 <- eval (extract v_4199 80 96);
      v_4206 <- eval (extract v_4199 96 112);
      v_4207 <- eval (extract v_4199 112 128);
      v_4208 <- eval (ult v_4206 v_4207);
      v_4209 <- eval (mux v_4208 v_4206 v_4207);
      v_4210 <- eval (ult v_4205 v_4209);
      v_4211 <- eval (mux v_4210 v_4205 v_4209);
      v_4212 <- eval (ult v_4204 v_4211);
      v_4213 <- eval (mux v_4212 v_4204 v_4211);
      v_4214 <- eval (ult v_4203 v_4213);
      v_4215 <- eval (mux v_4214 v_4203 v_4213);
      v_4216 <- eval (ult v_4202 v_4215);
      v_4217 <- eval (mux v_4216 v_4202 v_4215);
      v_4218 <- eval (ult v_4201 v_4217);
      v_4219 <- eval (mux v_4218 v_4201 v_4217);
      v_4220 <- eval (ult v_4200 v_4219);
      setRegister (lhs.of_reg v_2456) (concat (mux v_4220 (expression.bv_nat 112 7) (mux v_4218 (expression.bv_nat 112 6) (mux v_4216 (expression.bv_nat 112 5) (mux v_4214 (expression.bv_nat 112 4) (mux v_4212 (expression.bv_nat 112 3) (mux v_4210 (expression.bv_nat 112 2) (mux v_4208 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_4220 v_4200 v_4219));
      pure ()
    pat_end;
    pattern fun (v_2450 : Mem) (v_2451 : reg (bv 128)) => do
      v_11654 <- evaluateAddress v_2450;
      v_11655 <- load v_11654 16;
      v_11656 <- eval (extract v_11655 0 16);
      v_11657 <- eval (extract v_11655 16 32);
      v_11658 <- eval (extract v_11655 32 48);
      v_11659 <- eval (extract v_11655 48 64);
      v_11660 <- eval (extract v_11655 64 80);
      v_11661 <- eval (extract v_11655 80 96);
      v_11662 <- eval (extract v_11655 96 112);
      v_11663 <- eval (extract v_11655 112 128);
      v_11664 <- eval (ult v_11662 v_11663);
      v_11665 <- eval (mux v_11664 v_11662 v_11663);
      v_11666 <- eval (ult v_11661 v_11665);
      v_11667 <- eval (mux v_11666 v_11661 v_11665);
      v_11668 <- eval (ult v_11660 v_11667);
      v_11669 <- eval (mux v_11668 v_11660 v_11667);
      v_11670 <- eval (ult v_11659 v_11669);
      v_11671 <- eval (mux v_11670 v_11659 v_11669);
      v_11672 <- eval (ult v_11658 v_11671);
      v_11673 <- eval (mux v_11672 v_11658 v_11671);
      v_11674 <- eval (ult v_11657 v_11673);
      v_11675 <- eval (mux v_11674 v_11657 v_11673);
      v_11676 <- eval (ult v_11656 v_11675);
      setRegister (lhs.of_reg v_2451) (concat (mux v_11676 (expression.bv_nat 112 7) (mux v_11674 (expression.bv_nat 112 6) (mux v_11672 (expression.bv_nat 112 5) (mux v_11670 (expression.bv_nat 112 4) (mux v_11668 (expression.bv_nat 112 3) (mux v_11666 (expression.bv_nat 112 2) (mux v_11664 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_11676 v_11656 v_11675));
      pure ()
    pat_end
