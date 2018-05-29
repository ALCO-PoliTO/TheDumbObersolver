import java.util.ArrayList;

import ilog.concert.*;
import ilog.cp.*;

public class Main {

	public static void main(String[] args) {
		try {
			// OP(3,3,5) on (11-1)/2= 5 days
			// X_ij=1 i-th node is seated at place j-th
			IloCP cp = new IloCP();
			ArrayList<Integer> tables = new ArrayList<Integer>();
			tables.add(3);
			tables.add(3);
			tables.add(5);
			int seats = 0;
			for (int k = 0; k < tables.size(); k++)
				seats += tables.get(k);
			if (seats % 2 == 0) {
				System.out.println("!!--Size must be odd--!!");
				tables.set(0, tables.get(0) + 1);
				seats++;
			}
			int I = seats; // People
			int J = seats; // Seats
			int K = (seats - 1) / 2; // Days
			IloIntVar[][][] X = new IloIntVar[I][J][K];
			IloIntVar[][][] C = new IloIntVar[I][I][K];
			for (int i = 0; i < I; i++)
				for (int j = 0; j < J; j++)
					X[i][j] = cp.intVarArray(K, 0, 1, "X");

			for (int i = 0; i < I; i++)
				for (int j = 0; j < I; j++)
					C[i][j] = cp.intVarArray(K, 0, 1, "C");

			for (int k = 0; k < K; k++) {
				for (int i = 0; i < I; i++) {
					for (int j = 0; j < I; j++) {
						if (i == j)
							cp.add(cp.addEq(C[i][j][k], 0));
						else
							cp.add(cp.addEq(C[i][j][k], C[j][i][k]));
					}
				}
			}

			for (int i = 0; i < I; i++)
				for (int j = 0; j < J; j++)
					for (int k = 0; k < K; k++)
						X[i][j][k].setName("X_" + i + "_" + j + "_" + k);

			for (int i = 0; i < I; i++)
				for (int j = 0; j < I; j++)
					for (int k = 0; k < K; k++)
						C[i][j][k].setName("C_" + i + "_" + j + "_" + k);

			// Each player must seat in only one seat per day
			IloIntExpr[][] perDay = new IloIntExpr[I][K];
			for (int i = 0; i < I; i++) {
				for (int k = 0; k < K; k++) {
					perDay[i][k] = cp.intExpr();
					for (int j = 0; j < J; j++)
						perDay[i][k] = cp.sum(perDay[i][k], X[i][j][k]);
					cp.add(cp.eq(perDay[i][k], 1));
				}
			}

			// Each seat must be occupied by only one player each day
			IloIntExpr[][] perSeat = new IloIntExpr[J][K];
			for (int k = 0; k < K; k++) {
				for (int j = 0; j < J; j++) {
					perSeat[j][k] = cp.intExpr();
					for (int i = 0; i < I; i++)
						perSeat[j][k] = cp.sum(perSeat[j][k], X[i][j][k]);
					cp.add(cp.eq(perSeat[j][k], 1));
				}
			}

			// Each couple must appear once
			IloIntExpr[][] perCouple = new IloIntExpr[I][J];
			for (int i = 0; i < I; i++) {
				for (int j = 0; j < J && i > j; j++) {
					perCouple[i][j] = cp.intExpr();
					for (int k = 0; k < K; k++)
						perCouple[i][j] = cp.sum(perCouple[i][j], C[i][j][k]);
					cp.add(cp.eq(perCouple[i][j], 1));
				}
			}

			cp.add(cp.eq(X[0][0][0], 1));
			for (int t = 0; t < tables.get(0); t++) {
				int alpha = t % tables.get(0);
				int beta = (alpha + 1) % tables.get(0);
				for (int k = 0; k < K; k++) {
					for (int i = 0; i < I; i++) {
						for (int j = 0; j < I && i > j; j++) {
							// System.out.println("if X[" + i + "," + alpha + "," + k + "]==1 \t&&\t X[" + j
							// + "," + beta + ","
							// + k + "]==1 \t=> C[" + i + "," + j + "," + k + "]==1");
							cp.add(cp.ifThen(
									cp.or(cp.and(cp.eq(X[i][alpha][k], 1), cp.eq(X[j][beta][k], 1)),
											cp.and(cp.eq(X[i][beta][k], 1), cp.eq(X[j][alpha][k], 1))),
									cp.eq(C[i][j][k], 1)));
						}
					}
				}
			}
			for (int t = 0; t < tables.get(1); t++) {
				int alpha = (t % tables.get(1)) + tables.get(0);
				int beta = ((t % tables.get(1)) + 1) % tables.get(1) + tables.get(0);
				for (int k = 0; k < K; k++) {
					for (int i = 0; i < I; i++) {
						for (int j = 0; j < I && i > j; j++) {
							cp.add(cp.ifThen(
									cp.or(cp.and(cp.eq(X[i][alpha][k], 1), cp.eq(X[j][beta][k], 1)),
											cp.and(cp.eq(X[i][beta][k], 1), cp.eq(X[j][alpha][k], 1))),
									cp.eq(C[i][j][k], 1)));
						}
					}
				}
			}

			for (int t = 0; t < tables.get(2); t++) {
				int alpha = (t % tables.get(2)) + tables.get(0) + tables.get(1);
				int beta = ((t % tables.get(2)) + 1) % tables.get(2) + tables.get(0) + tables.get(1);
				for (int k = 0; k < K; k++) {
					for (int i = 0; i < I; i++) {
						for (int j = 0; j < I && i > j; j++) {
							cp.add(cp.ifThen(
									cp.or(cp.and(cp.eq(X[i][alpha][k], 1), cp.eq(X[j][beta][k], 1)),
											cp.and(cp.eq(X[i][beta][k], 1), cp.eq(X[j][alpha][k], 1))),
									cp.eq(C[i][j][k], 1)));
						}
					}
				}
			}

			cp.exportModel("OP_" + tables.get(0) + "_" + tables.get(1) + "_" + tables.get(2) + ".cpo");
			cp.setParameter(IloCP.IntParam.LogPeriod, 100000);
			cp.propagate();

			if (cp.solve()) {
				System.out.println("Solution found.");
				for (int k = 0; k < K; k++) {
					System.out.println("Day " + (k + 1));
					System.out.println("\tTable of " + tables.get(0));
					for (int t = 0; t < tables.get(0); t++) {
						for (int i = 0; i < I; i++)
							if (cp.getIntValue(X[i][t][k]) == 1)
								System.out.println("\t\tSeat " + t + ": " + i);
					}

					System.out.println("\tTable of " + tables.get(1));
					for (int t = tables.get(0); t < (tables.get(0) + tables.get(1)); t++) {
						for (int i = 0; i < I; i++)
							if (cp.getIntValue(X[i][t][k]) == 1)
								System.out.println("\t\tSeat " + t + ": " + i);
					}
					System.out.println("\tTable of " + tables.get(2));
					for (int t = (tables.get(0) + tables.get(1)); t < (tables.get(0) + tables.get(1)
							+ tables.get(2)); t++) {
						for (int i = 0; i < I; i++)
							if (cp.getIntValue(X[i][t][k]) == 1)
								System.out.println("\t\tSeat " + t + ": " + i);
					}
				}

			}

		} catch (IloException e) {
			System.out.println("Error : " + e);
			e.printStackTrace();
		}
	}
}
